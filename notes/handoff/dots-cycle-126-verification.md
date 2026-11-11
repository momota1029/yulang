# Cycle126 local verification evidence

This report transcribes existing local logs and exit-status files. No tests, builds, Git mutations, or repository edits were run to produce this report. Publication and hosted CI status are deliberately left to the parent report.

## Final scope and result

- Focused final build: exit 0, 553 reported Lake jobs, targeting 17 modules. This is a focused dependency build, not a full workspace build.
- Final named-theorem audit: exit 0; 109 audit entries and 109 requested names. Exact ordered name equality: True.
- Only propext, Classical.choice, and Quot.sound appear in the final theorem dependencies. No sorryAx or other forbidden axiom appears.
- Three executable definitions were separately audited; their dependencies are propext and Quot.sound only.
- Corrected final signatures command: exit 0.
- Runtime regression log: exit 0, [true, false, false, false, false].
- Final diff-only repository gate: exit 0 after commit 220f63ba9. Its PASS explicitly excludes a build.
- git diff --check: exit 0, empty output.

Local full build, full Audit.lean, and independent AxiomGate were NOT run. A focused audit of these 109 named theorems is not the full Audit or independent AxiomGate. These results do not certify general B4 completion, candidate selection, capture discovery, or general head matching.

## Seventeen modules

- Yulang.GeneralDictionaryBinderOnlyBoundary
- Yulang.GeneralDictionaryComputedOutputExamples
- Yulang.GeneralDictionaryComputedOutputPlans
- Yulang.GeneralDictionaryComputedTransactions
- Yulang.GeneralDictionaryPreparationExamples
- Yulang.GeneralDictionaryTerminalFixture
- Yulang.GeneralDictionaryVariableCompatibility
- Yulang.GeneralDictionaryVariableExamples
- Yulang.GeneralDictionaryVariableMaterialization
- Yulang.GeneralDictionaryVariableOrder
- Yulang.GeneralDictionaryVariablePlans
- Yulang.GeneralDictionaryVariablePreparation
- Yulang.GeneralDictionaryVariableRealization
- Yulang.GeneralDictionaryVariableTerms
- Yulang.GeneralDictionaryVariableTransactions
- Yulang.GeneralDictionaryVariableHeads
- Yulang.GeneralDictionaryHeadExamples

## Final command provenance

Working directory: /workspace/scratch/1d0b4aaa3394/yulang. The following executed command text was confirmed by the parent that ran the checks. Logs capture stdout and stderr together.

```bash
export PATH=/workspace/scratch/1d0b4aaa3394/cache/toolchain116/lean-4.35.0-linux/bin:$PATH
set +e
timeout 180 bash -c 'cd lean && lake build $(cat ../cache/yulang126/final-modules.txt) --wfail' >cache/yulang126/final-build.log 2>&1
echo $? >cache/yulang126/final-build.exit
timeout 180 bash -c 'cd lean && lake env lean --trust=0 -j1 ../cache/yulang126/FinalAudit.lean' >cache/yulang126/final-audit.log 2>&1
echo $? >cache/yulang126/final-audit.exit
(cd lean && timeout 120 lake env lean --trust=0 -j1 ../cache/yulang126/FinalSignatures.lean) >cache/yulang126/final-signatures.log 2>&1
echo $? >cache/yulang126/final-signatures.exit
```

The parent additionally confirmed these executed command cores. Redirection/status-capture wrapper text was not supplied verbatim for these commands:

```bash
timeout 120 bash -c 'cd lean && lake env lean --trust=0 -j1 ../cache/yulang126/RuntimeAudit.lean'
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
git diff --check
```

Runtime.lean: the original launch command was not retained in the available context. The existing log and exit status below are observed evidence. The following is a reconstructed reproduction command, NOT claimed as the exact executed command:

```bash
cd /workspace/scratch/1d0b4aaa3394/yulang/lean
PATH=/workspace/scratch/1d0b4aaa3394/cache/toolchain116/lean-4.35.0-linux/bin:$PATH timeout 120 lake env lean --trust=0 -j1 ../cache/yulang126/Runtime.lean
```

## Complete final logs

### final-build

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
Build completed successfully (553 jobs).
```

### final-audit

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
'Yulang.GeneralDictionaryBinderOnlyBoundary.output_requires_nonempty_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBinderOnlyBoundary.built_root_outputs_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.actual_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.absent_key_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.wrong_role_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.computes_repeated_outputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.retains_distinct_targets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.supplies_complete_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.supplies_concrete_terms' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.same_visible_declaration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_computed_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_repeated_targets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.missing_binder_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.build_head' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_output_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.built_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.transaction_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.lifted_source_instance' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.transaction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.source_instance_declaration' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.source_output_denotes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPreparationExamples.child_prepares' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryPreparationExamples.tree_prepares' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryPreparationExamples.missing_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPreparationExamples.extra_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPreparationExamples.wrong_identity_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPreparationExamples.missing_key_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryPreparationExamples.unequal_leaf_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryPreparationExamples.recipe_heads' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryPreparationExamples.prepared_built' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.leaf_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.root_actual_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.child_actual_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.root_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.child_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.joint_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.tree_items' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.tree_joint_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.retained_outputs' depends on axioms: [propext]
'Yulang.GeneralDictionaryTerminalFixture.root_build' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.child_build' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.root_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.child_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.tree_built' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.uniform_completion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.all_model_root_child_input' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableCompatibility.compile_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableCompatibility.build_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.singleton_input_lookup' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.unequal_input_deferred' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.output_binder_unchanged' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.compound_deferred' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.default_deferred' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.nonidentity_input_compiles' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.nonidentity_input_build' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableMaterialization.compile_slot_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableMaterialization.compile_variable' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableMaterialization.build_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableMaterialization.build_none_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableMaterialization.plan_lookup_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableOrder.bodyTerm_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableOrder.term_lookup_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableOrder.compile_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableOrder.build_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableOrder.lookup_reorders_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableOrder.lookup_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariablePlans.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariablePlans.build_head' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariablePlans.lookup_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariablePlans.lookup_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariablePlans.lookup_output_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariablePreparation.prepare_node_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariablePreparation.prepare_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariablePreparation.prepare_built' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariablePreparation.prepare_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableRealization.singleton_value' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableRealization.denotes_realization' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableRealization.built_output_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.output_lookup_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.compile_interpreted' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.build_interpreted' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.build_head' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.build_output_denotes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.built_output_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTransactions.built_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTransactions.transaction_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTransactions.lifted_source_instance' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTransactions.transaction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTransactions.source_instance_declaration' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTransactions.source_output_denotes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableHeads.compileAt_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableHeads.build_head_denotes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableHeads.build_preserves' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableHeads.build_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableHeads.denotesAt_realization' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadExamples.leaf_positional_compiles' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadExamples.leaf_head_denotes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadExamples.leaf_head_builds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadExamples.leaf_concrete_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadExamples.nominal_root_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadExamples.unequal_leaf_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadExamples.absent_source_defers' depends on axioms: [propext, Quot.sound]
```

### runtime-audit

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
'Yulang.GeneralDictionaryVariablePreparation.prepare' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableHeads.build' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.build' depends on axioms: [propext, Quot.sound]
```

### runtime

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
[true, false, false, false, false]
```

### final-gate

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
verify-lean: . @ 220f63ba9 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

### final-diff

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
```

The log is empty; no output was recorded.

### final-signatures

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
@Yulang.GeneralDictionaryBinderOnlyBoundary.output_requires_nonempty_child : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {constructors : Yulang.GeneralDeclarationPatterns.Constructors}
  (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (located : Yulang.GeneralDictionaryStateEquations.Located state root.demand),
  Yulang.GeneralDictionaryOutputBinderTerms.Interpreted declaration (frame.capture declaration.id) located →
    ∀ (index : Fin root.demand.outputs.length),
      ∃ child,
        child ∈ Yulang.GeneralDictionaryEmissionPlans.children frame root declaration checked ∧
          child.demand.outputs ≠ []
@Yulang.GeneralDictionaryBinderOnlyBoundary.built_root_outputs_empty : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryComputedTransactions.Built registry checked frames heads tree → tree.root.demand.outputs = []
Yulang.GeneralDictionaryComputedOutputExamples.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryComputedOutputExamples.registry
Yulang.GeneralDictionaryComputedOutputExamples.actual_lookup : Yulang.GeneralDictionaryComputedOutputPlans.lookup
    Yulang.GeneralDictionaryComputedOutputExamples.registry
    Yulang.GeneralDictionaryComputedOutputExamples.registry_checked Yulang.GeneralDictionaryComputedOutputExamples.frame
    Yulang.GeneralDictionaryComputedOutputExamples.root 2 Yulang.GeneralDictionaryBinderLocationExamples.inputs =
  some Yulang.GeneralDictionaryComputedOutputExamples.result
Yulang.GeneralDictionaryComputedOutputExamples.absent_key_defers : Yulang.GeneralDictionaryComputedOutputPlans.lookup
    Yulang.GeneralDictionaryComputedOutputExamples.registry
    Yulang.GeneralDictionaryComputedOutputExamples.registry_checked Yulang.GeneralDictionaryComputedOutputExamples.frame
    Yulang.GeneralDictionaryComputedOutputExamples.root 99 Yulang.GeneralDictionaryBinderLocationExamples.inputs =
  none
Yulang.GeneralDictionaryComputedOutputExamples.wrong_role_defers : Yulang.GeneralDictionaryComputedOutputPlans.lookup
    Yulang.GeneralDictionaryComputedOutputExamples.registry
    Yulang.GeneralDictionaryComputedOutputExamples.registry_checked Yulang.GeneralDictionaryComputedOutputExamples.frame
    Yulang.GeneralDictionaryComputedOutputExamples.root 1 Yulang.GeneralDictionaryBinderLocationExamples.inputs =
  none
Yulang.GeneralDictionaryComputedOutputExamples.computes_repeated_outputs : Option.map
    (fun r => [r.located.output ⟨0, ⋯⟩, r.located.output ⟨1, ⋯⟩])
    (Yulang.GeneralDictionaryComputedOutputPlans.lookup Yulang.GeneralDictionaryComputedOutputExamples.registry
      Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
      Yulang.GeneralDictionaryComputedOutputExamples.frame Yulang.GeneralDictionaryComputedOutputExamples.root 2
      Yulang.GeneralDictionaryBinderLocationExamples.inputs) =
  some [Yulang.Core.PresenceGeneration.TyTerm.var 2, Yulang.Core.PresenceGeneration.TyTerm.var 2]
Yulang.GeneralDictionaryComputedOutputExamples.retains_distinct_targets : Option.map
    (fun r =>
      [Yulang.GeneralDictionaryOutputBinderExamples.state.source (r.located.target ⟨0, ⋯⟩),
        Yulang.GeneralDictionaryOutputBinderExamples.state.source (r.located.target ⟨1, ⋯⟩)])
    (Yulang.GeneralDictionaryComputedOutputPlans.lookup Yulang.GeneralDictionaryComputedOutputExamples.registry
      Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
      Yulang.GeneralDictionaryComputedOutputExamples.frame Yulang.GeneralDictionaryComputedOutputExamples.root 2
      Yulang.GeneralDictionaryBinderLocationExamples.inputs) =
  some [3, 4]
Yulang.GeneralDictionaryComputedOutputExamples.supplies_complete_plan : Yulang.GeneralDictionaryEmissionPlans.Plan
  Yulang.GeneralDictionaryComputedOutputExamples.registry
  Yulang.GeneralDictionaryComputedOutputExamples.registry_checked Yulang.GeneralDictionaryComputedOutputExamples.frame
  Yulang.GeneralDictionaryComputedOutputExamples.root 2 Yulang.GeneralDictionaryComputedOutputExamples.result.children
Yulang.GeneralDictionaryComputedOutputExamples.supplies_concrete_terms : ∀
  (heads :
    Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryOutputBinderExamples.state),
  heads Yulang.GeneralDictionaryComputedOutputExamples.root Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
      Yulang.GeneralDictionaryOutputBinderExamples.capture Yulang.GeneralDictionaryBinderLocationExamples.inputs.head →
    Yulang.GeneralDictionaryComputedOutputPlans.Terms Yulang.GeneralDictionaryComputedOutputExamples.registry
      (fun x => Yulang.GeneralDictionaryComputedOutputExamples.frame) heads
      Yulang.GeneralDictionaryComputedOutputExamples.root 2
      Yulang.GeneralDictionaryComputedOutputExamples.result.located
Yulang.GeneralDictionaryComputedOutputExamples.same_visible_declaration : ∃ declaration _present,
  declaration.id = 2 ∧
    declaration.role = Yulang.GeneralDictionaryComputedOutputExamples.root.demand.role ∧
      Yulang.GeneralDictionaryPlannedOutputs.OutputPlan Yulang.GeneralDictionaryComputedOutputExamples.registry
          Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
          Yulang.GeneralDictionaryComputedOutputExamples.frame Yulang.GeneralDictionaryComputedOutputExamples.root 2
          (Yulang.GeneralDictionaryComputedOutputExamples.result.children,
            Yulang.GeneralDictionaryAssociatedProvenance.outputs Yulang.GeneralDeclarationExamples.roles declaration
              Yulang.GeneralDictionaryComputedOutputExamples.root.demand) ∧
        Yulang.GeneralDictionaryOutputBinderTerms.Interpreted declaration
          (Yulang.GeneralDictionaryComputedOutputExamples.frame.capture declaration.id)
          Yulang.GeneralDictionaryComputedOutputExamples.result.located
Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_lookup : Yulang.GeneralDictionaryComputedOutputPlans.lookup
    Yulang.GeneralDictionaryComputedOutputExamples.registry
    Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
    Yulang.GeneralDictionaryComputedOutputExamples.shiftedFrame
    Yulang.GeneralDictionaryComputedOutputExamples.shiftedRoot 2
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedInputs =
  some Yulang.GeneralDictionaryComputedOutputExamples.shiftedResult
Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_computed_output : Option.map
    (fun r =>
      Yulang.GeneralDictionaryStateEquations.liftType Yulang.GeneralDictionaryBinderLocationExamples.shiftedState
        (r.located.output ⟨0, ⋯⟩))
    (Yulang.GeneralDictionaryComputedOutputPlans.lookup Yulang.GeneralDictionaryComputedOutputExamples.registry
      Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
      Yulang.GeneralDictionaryComputedOutputExamples.shiftedFrame
      Yulang.GeneralDictionaryComputedOutputExamples.shiftedRoot 2
      Yulang.GeneralDictionaryBinderLocationExamples.shiftedInputs) =
  some (Yulang.Core.PresenceGeneration.TyTerm.var 12)
Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_repeated_targets : Option.map
    (fun r =>
      [Yulang.GeneralDictionaryBinderLocationExamples.shiftedState.source (r.located.target ⟨0, ⋯⟩),
        Yulang.GeneralDictionaryBinderLocationExamples.shiftedState.source (r.located.target ⟨1, ⋯⟩)])
    (Yulang.GeneralDictionaryComputedOutputPlans.lookup Yulang.GeneralDictionaryComputedOutputExamples.registry
      Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
      Yulang.GeneralDictionaryComputedOutputExamples.shiftedFrame
      Yulang.GeneralDictionaryComputedOutputExamples.shiftedRoot 2
      Yulang.GeneralDictionaryBinderLocationExamples.shiftedInputs) =
  some [13, 14]
Yulang.GeneralDictionaryComputedOutputExamples.missing_binder_defers : Yulang.GeneralDictionaryComputedOutputPlans.lookup
    Yulang.GeneralDictionaryComputedOutputExamples.registry
    Yulang.GeneralDictionaryComputedOutputExamples.registry_checked
    Yulang.GeneralDictionaryComputedOutputExamples.absentFrame
    Yulang.GeneralDictionaryComputedOutputExamples.shiftedRoot 2
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedInputs =
  none
@Yulang.GeneralDictionaryComputedOutputPlans.lookup_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryComputedOutputPlans.Result state root),
  Yulang.GeneralDictionaryComputedOutputPlans.lookup registry checked frame root key inputs = some result ↔
    ∃ declaration present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          Yulang.GeneralDictionaryBinderLocations.build declaration (frame.capture declaration.id) inputs =
              some result.located ∧
            result.children = Yulang.GeneralDictionaryEmissionPlans.children frame root declaration ⋯
@Yulang.GeneralDictionaryComputedOutputPlans.build_head : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
  Yulang.GeneralDictionaryBinderLocations.build declaration capture inputs = some located → located.head = inputs.head
@Yulang.GeneralDictionaryComputedOutputPlans.lookup_plan : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryComputedOutputPlans.Result state root),
  Yulang.GeneralDictionaryComputedOutputPlans.lookup registry checked frame root key inputs = some result →
    Yulang.GeneralDictionaryEmissionPlans.Plan registry checked frame root key result.children
@Yulang.GeneralDictionaryComputedOutputPlans.lookup_terms : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryComputedOutputPlans.Result state root),
  Yulang.GeneralDictionaryComputedOutputPlans.lookup registry checked (frames root) root key inputs = some result →
    (∀ (declaration : Yulang.GeneralDeclarations.Declaration),
        declaration ∈ registry.declarations →
          declaration.id = key →
            declaration.role = root.demand.role →
              heads root declaration ((frames root).capture declaration.id) inputs.head) →
      Yulang.GeneralDictionaryComputedOutputPlans.Terms registry frames heads root key result.located
@Yulang.GeneralDictionaryComputedOutputPlans.lookup_output_plan : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryComputedOutputPlans.Result state root),
  Yulang.GeneralDictionaryComputedOutputPlans.lookup registry checked frame root key inputs = some result →
    ∃ declaration _present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          Yulang.GeneralDictionaryPlannedOutputs.OutputPlan registry checked frame root key
              (result.children,
                Yulang.GeneralDictionaryAssociatedProvenance.outputs registry.roles declaration root.demand) ∧
            Yulang.GeneralDictionaryOutputBinderTerms.Interpreted declaration (frame.capture declaration.id)
              result.located
@Yulang.GeneralDictionaryComputedTransactions.built_valid : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryComputedTransactions.Built registry checked frames heads tree →
    Yulang.GeneralDictionaryTransactions.Valid registry checked frames
      (Yulang.GeneralDictionaryComputedOutputPlans.Terms registry frames heads) tree
@Yulang.GeneralDictionaryComputedTransactions.transaction_stored : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryComputedTransactions.Built registry checked frames heads tree →
    Yulang.GeneralSourceDictionaries.Evidence
      (Yulang.GeneralDictionaryModelEvidence.StoredInstance
        (Yulang.GeneralDictionaryTransactions.PlannedAt registry checked frames
          (Yulang.GeneralDictionaryTransactions.LiftedTerms tree.items
            (Yulang.GeneralDictionaryComputedOutputPlans.Terms registry frames heads))))
      tree.dictionary
@Yulang.GeneralDictionaryComputedTransactions.lifted_source_instance : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (items : List (Yulang.GeneralDictionaryBatchRecording.Item registry.roles state))
  (assignment : Yulang.GeneralSourceState.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralDictionaryModelEvidence.ModelInstance
      (Yulang.GeneralDictionaryTransactions.PlannedAt registry checked frames
        (Yulang.GeneralDictionaryTransactions.LiftedTerms items
          (Yulang.GeneralDictionaryComputedOutputPlans.Terms registry frames heads)))
      assignment root key children →
    Yulang.GeneralDictionaryComputedTransactions.SourceInstance registry checked frames heads assignment root key
      children
@Yulang.GeneralDictionaryComputedTransactions.transaction_uniform : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryComputedTransactions.Built registry checked frames heads tree →
    ∃ witness,
      Yulang.GeneralSourceDictionaries.Readback tree.root (Yulang.GeneralSourceDictionaries.erase tree.dictionary)
          witness ∧
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryBatchRecording.record tree.items) assignment →
            Yulang.GeneralSourceDictionaries.Evidence
              (Yulang.GeneralDictionaryComputedTransactions.SourceInstance registry checked frames heads assignment)
              witness
@Yulang.GeneralDictionaryComputedTransactions.source_instance_declaration : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (assignment : Yulang.GeneralSourceState.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralDictionaryComputedTransactions.SourceInstance registry checked frames heads assignment root key
      children →
    ∃ declaration present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          children = Yulang.GeneralDictionaryEmissionPlans.children (frames root) root declaration ⋯ ∧
            ∃ located,
              heads root declaration ((frames root).capture declaration.id) located.head ∧
                Yulang.GeneralDictionaryOutputBinderTerms.Interpreted declaration ((frames root).capture declaration.id)
                    located ∧
                  located.equations.Holds assignment
@Yulang.GeneralDictionaryComputedTransactions.source_output_denotes : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryComputedOutputPlans.HeadInstances registry.roles state)
  (assignment : Yulang.GeneralSourceState.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralDictionaryComputedTransactions.SourceInstance registry checked frames heads assignment root key
      children →
    ∀ (index : Fin root.demand.outputs.length),
      ∃ declaration present,
        declaration.id = key ∧
          declaration.role = root.demand.role ∧
            children = Yulang.GeneralDictionaryEmissionPlans.children (frames root) root declaration ⋯ ∧
              ∃ term,
                Yulang.GeneralDictionaryOutputBinderTerms.Denotes registry.roles declaration
                    ((frames root).capture declaration.id) root.demand.outputs[index].name term ∧
                  Yulang.Common.Equivalent (assignment root.demand.outputs[index].target).fst
                    (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment term)
Yulang.GeneralDictionaryPreparationExamples.child_prepares : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryTerminalFixture.frame) Yulang.GeneralDictionaryPreparationExamples.childRecipe =
  some
    (Yulang.GeneralDictionaryTransactions.Prepared.node Yulang.GeneralDictionaryTerminalFixture.child 3
      Yulang.GeneralDictionaryTerminalFixture.childLocated [])
Yulang.GeneralDictionaryPreparationExamples.tree_prepares : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryTerminalFixture.frame) Yulang.GeneralDictionaryPreparationExamples.recipe =
  some Yulang.GeneralDictionaryTerminalFixture.tree
Yulang.GeneralDictionaryPreparationExamples.missing_child_defers : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryTerminalFixture.frame)
    (Yulang.GeneralDictionaryVariablePreparation.Recipe.node Yulang.GeneralDictionaryTerminalFixture.root 2
      Yulang.GeneralDictionaryTerminalFixture.rootInputs []) =
  none
Yulang.GeneralDictionaryPreparationExamples.extra_child_defers : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryTerminalFixture.frame)
    (Yulang.GeneralDictionaryVariablePreparation.Recipe.node Yulang.GeneralDictionaryTerminalFixture.root 2
      Yulang.GeneralDictionaryTerminalFixture.rootInputs
      [Yulang.GeneralDictionaryPreparationExamples.childRecipe,
        Yulang.GeneralDictionaryPreparationExamples.childRecipe]) =
  none
Yulang.GeneralDictionaryPreparationExamples.wrong_identity_defers : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryTerminalFixture.frame)
    (Yulang.GeneralDictionaryVariablePreparation.Recipe.node Yulang.GeneralDictionaryTerminalFixture.root 2
      Yulang.GeneralDictionaryTerminalFixture.rootInputs
      [Yulang.GeneralDictionaryVariablePreparation.Recipe.node Yulang.GeneralDictionaryPreparationExamples.wrongChild 3
          Yulang.GeneralDictionaryTerminalFixture.childInputs []]) =
  none
Yulang.GeneralDictionaryPreparationExamples.missing_key_defers : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryTerminalFixture.frame)
    (Yulang.GeneralDictionaryVariablePreparation.Recipe.node Yulang.GeneralDictionaryTerminalFixture.root 99
      Yulang.GeneralDictionaryTerminalFixture.rootInputs [Yulang.GeneralDictionaryPreparationExamples.childRecipe]) =
  none
Yulang.GeneralDictionaryPreparationExamples.unequal_leaf_defers : Yulang.GeneralDictionaryVariablePreparation.prepare
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    (fun x => Yulang.GeneralDictionaryPreparationExamples.unequalFrame)
    Yulang.GeneralDictionaryPreparationExamples.childRecipe =
  none
Yulang.GeneralDictionaryPreparationExamples.recipe_heads : ∀
  (heads :
    Yulang.GeneralDictionaryVariablePlans.HeadInstances Yulang.GeneralDictionaryTerminalFixture.registry.roles
      Yulang.GeneralDictionaryTerminalFixture.state),
  heads Yulang.GeneralDictionaryTerminalFixture.root Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
      Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.rootInputs.head →
    heads Yulang.GeneralDictionaryTerminalFixture.child Yulang.GeneralDictionaryTerminalFixture.leaf
        Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.childInputs.head →
      Yulang.GeneralDictionaryVariablePreparation.Heads Yulang.GeneralDictionaryTerminalFixture.registry
        (fun x => Yulang.GeneralDictionaryTerminalFixture.frame) heads
        Yulang.GeneralDictionaryPreparationExamples.recipe
Yulang.GeneralDictionaryPreparationExamples.prepared_built : ∀
  (heads :
    Yulang.GeneralDictionaryVariablePlans.HeadInstances Yulang.GeneralDictionaryTerminalFixture.registry.roles
      Yulang.GeneralDictionaryTerminalFixture.state),
  heads Yulang.GeneralDictionaryTerminalFixture.root Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
      Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.rootInputs.head →
    heads Yulang.GeneralDictionaryTerminalFixture.child Yulang.GeneralDictionaryTerminalFixture.leaf
        Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.childInputs.head →
      Yulang.GeneralDictionaryVariableTransactions.Built Yulang.GeneralDictionaryTerminalFixture.registry
        Yulang.GeneralDictionaryTerminalFixture.registry_checked
        (fun x => Yulang.GeneralDictionaryTerminalFixture.frame) heads Yulang.GeneralDictionaryTerminalFixture.tree
Yulang.GeneralDictionaryTerminalFixture.leaf_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryTerminalFixture.leaf
Yulang.GeneralDictionaryTerminalFixture.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryTerminalFixture.registry
Yulang.GeneralDictionaryTerminalFixture.root_actual_children : Yulang.GeneralDictionaryEmissionPlans.children
    Yulang.GeneralDictionaryTerminalFixture.frame Yulang.GeneralDictionaryTerminalFixture.root
    Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
    Yulang.GeneralDictionaryOutputBinderExamples.binderWrap_checked =
  [Yulang.GeneralDictionaryTerminalFixture.child]
Yulang.GeneralDictionaryTerminalFixture.child_actual_children : Yulang.GeneralDictionaryEmissionPlans.children
    Yulang.GeneralDictionaryTerminalFixture.frame Yulang.GeneralDictionaryTerminalFixture.child
    Yulang.GeneralDictionaryTerminalFixture.leaf Yulang.GeneralDictionaryTerminalFixture.leaf_checked =
  []
Yulang.GeneralDictionaryTerminalFixture.root_holds : Yulang.GeneralDictionaryTerminalFixture.rootLocated.equations.Holds
  Yulang.GeneralDictionaryTerminalFixture.assignment
Yulang.GeneralDictionaryTerminalFixture.child_holds : Yulang.GeneralDictionaryTerminalFixture.childLocated.equations.Holds
  Yulang.GeneralDictionaryTerminalFixture.assignment
Yulang.GeneralDictionaryTerminalFixture.joint_model : Yulang.GeneralSourceState.Models
  (Yulang.GeneralDictionaryBatchRecording.record
    [Yulang.GeneralDictionaryTerminalFixture.rootItem, Yulang.GeneralDictionaryTerminalFixture.childItem])
  Yulang.GeneralDictionaryTerminalFixture.assignment
Yulang.GeneralDictionaryTerminalFixture.tree_items : Yulang.GeneralDictionaryTerminalFixture.tree.items =
  [Yulang.GeneralDictionaryTerminalFixture.rootItem, Yulang.GeneralDictionaryTerminalFixture.childItem]
Yulang.GeneralDictionaryTerminalFixture.tree_joint_model : Yulang.GeneralSourceState.Models
  (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryTerminalFixture.tree.items)
  Yulang.GeneralDictionaryTerminalFixture.assignment
Yulang.GeneralDictionaryTerminalFixture.retained_outputs : Yulang.GeneralDictionaryTerminalFixture.rootDemand.outputs =
    [{ name := 0, target := 3 }, { name := 0, target := 4 }] ∧
  Yulang.GeneralDictionaryTerminalFixture.childDemand.outputs = [{ name := 1, target := 2 }]
Yulang.GeneralDictionaryTerminalFixture.root_build : Yulang.GeneralDictionaryVariableTerms.build
    Yulang.GeneralDictionaryOutputBinderExamples.binderWrap Yulang.GeneralDictionaryTerminalFixture.capture
    Yulang.GeneralDictionaryTerminalFixture.rootInputs =
  some Yulang.GeneralDictionaryTerminalFixture.rootLocated
Yulang.GeneralDictionaryTerminalFixture.child_build : Yulang.GeneralDictionaryVariableTerms.build
    Yulang.GeneralDictionaryTerminalFixture.leaf Yulang.GeneralDictionaryTerminalFixture.capture
    Yulang.GeneralDictionaryTerminalFixture.childInputs =
  some Yulang.GeneralDictionaryTerminalFixture.childLocated
Yulang.GeneralDictionaryTerminalFixture.root_lookup : Yulang.GeneralDictionaryVariablePlans.lookup
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    Yulang.GeneralDictionaryTerminalFixture.frame Yulang.GeneralDictionaryTerminalFixture.root 2
    Yulang.GeneralDictionaryTerminalFixture.rootInputs =
  some Yulang.GeneralDictionaryTerminalFixture.rootResult
Yulang.GeneralDictionaryTerminalFixture.child_lookup : Yulang.GeneralDictionaryVariablePlans.lookup
    Yulang.GeneralDictionaryTerminalFixture.registry Yulang.GeneralDictionaryTerminalFixture.registry_checked
    Yulang.GeneralDictionaryTerminalFixture.frame Yulang.GeneralDictionaryTerminalFixture.child 3
    Yulang.GeneralDictionaryTerminalFixture.childInputs =
  some Yulang.GeneralDictionaryTerminalFixture.childResult
Yulang.GeneralDictionaryTerminalFixture.tree_built : ∀
  (heads :
    Yulang.GeneralDictionaryVariablePlans.HeadInstances Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryTerminalFixture.state),
  heads Yulang.GeneralDictionaryTerminalFixture.root Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
      Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.rootInputs.head →
    heads Yulang.GeneralDictionaryTerminalFixture.child Yulang.GeneralDictionaryTerminalFixture.leaf
        Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.childInputs.head →
      Yulang.GeneralDictionaryVariableTransactions.Built Yulang.GeneralDictionaryTerminalFixture.registry
        Yulang.GeneralDictionaryTerminalFixture.registry_checked
        (fun x => Yulang.GeneralDictionaryTerminalFixture.frame) heads Yulang.GeneralDictionaryTerminalFixture.tree
Yulang.GeneralDictionaryTerminalFixture.uniform_completion : ∀
  (heads :
    Yulang.GeneralDictionaryVariablePlans.HeadInstances Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryTerminalFixture.state),
  heads Yulang.GeneralDictionaryTerminalFixture.root Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
      Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.rootInputs.head →
    heads Yulang.GeneralDictionaryTerminalFixture.child Yulang.GeneralDictionaryTerminalFixture.leaf
        Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.childInputs.head →
      ∃ witness,
        Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionaryTerminalFixture.tree.root
            (Yulang.GeneralSourceDictionaries.erase Yulang.GeneralDictionaryTerminalFixture.tree.dictionary) witness ∧
          ∀ (model : Yulang.GeneralSourceState.Assignment),
            Yulang.GeneralSourceState.Models
                (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryTerminalFixture.tree.items)
                model →
              Yulang.GeneralSourceDictionaries.Evidence
                (Yulang.GeneralDictionaryVariableTransactions.SourceInstance
                  Yulang.GeneralDictionaryTerminalFixture.registry
                  Yulang.GeneralDictionaryTerminalFixture.registry_checked
                  (fun x => Yulang.GeneralDictionaryTerminalFixture.frame) heads model)
                witness
Yulang.GeneralDictionaryTerminalFixture.all_model_root_child_input : ∀ (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models
      (Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryTerminalFixture.tree.items) model →
    ∀ (index : Fin Yulang.GeneralDictionaryTerminalFixture.rootDemand.outputs.length),
      Yulang.Common.Equivalent (model Yulang.GeneralDictionaryTerminalFixture.rootDemand.outputs[index].target).fst
          (model 2).fst ∧
        Yulang.Common.Equivalent (model 2).fst (model 0).fst ∧
          Yulang.Common.Equivalent (model Yulang.GeneralDictionaryTerminalFixture.rootDemand.outputs[index].target).fst
            (model 0).fst
Yulang.GeneralDictionaryVariableCompatibility.compile_preserved : ∀ (state : Yulang.GeneralSourceState.State)
  (roles : Yulang.Roles.RoleDecls) (declaration : Yulang.GeneralDeclarations.Declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (name : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
      Yulang.GeneralDictionaryBinderLocations.compile state roles declaration capture name = some term →
        Yulang.GeneralDictionaryVariableTerms.compile state roles declaration capture name = some term
@Yulang.GeneralDictionaryVariableCompatibility.build_preserved : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
      (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
      Yulang.GeneralDictionaryBinderLocations.build declaration capture inputs = some located →
        Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located
Yulang.GeneralDictionaryVariableExamples.singleton_input_lookup : Yulang.GeneralDictionaryVariableTerms.lookup
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryOutputBinderExamples.inputWrap
    Yulang.GeneralDictionaryVariableExamples.singletonCapture 0 =
  some (Yulang.Core.PresenceGeneration.TyTerm.var 12)
Yulang.GeneralDictionaryVariableExamples.unequal_input_deferred : Yulang.GeneralDictionaryVariableTerms.lookup
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryOutputBinderExamples.inputWrap
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedCapture 0 =
  none
Yulang.GeneralDictionaryVariableExamples.output_binder_unchanged : Yulang.GeneralDictionaryVariableTerms.lookup
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedCapture 0 =
  some (Yulang.Core.PresenceGeneration.TyTerm.var 12)
Yulang.GeneralDictionaryVariableExamples.compound_deferred : Yulang.GeneralDictionaryVariableTerms.lookup
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDeclarationExamples.wrap
    Yulang.GeneralDictionaryVariableExamples.singletonCapture 0 =
  none
Yulang.GeneralDictionaryVariableExamples.default_deferred : Yulang.GeneralDictionaryVariableTerms.lookup
    Yulang.GeneralDictionaryOutputBinderExamples.defaultRoles Yulang.GeneralDictionaryOutputBinderExamples.defaultWrap
    Yulang.GeneralDictionaryVariableExamples.singletonCapture 0 =
  none
Yulang.GeneralDictionaryVariableExamples.nonidentity_input_compiles : Yulang.GeneralDictionaryVariableTerms.compile
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedState Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryOutputBinderExamples.inputWrap Yulang.GeneralDictionaryVariableExamples.singletonCapture 0 =
  some (Yulang.Core.PresenceGeneration.TyTerm.var 2)
Yulang.GeneralDictionaryVariableExamples.nonidentity_input_build : Yulang.GeneralDictionaryVariableTerms.build
    Yulang.GeneralDictionaryOutputBinderExamples.inputWrap Yulang.GeneralDictionaryVariableExamples.singletonCapture
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedInputs =
  some Yulang.GeneralDictionaryBinderLocationExamples.shiftedLocated
Yulang.GeneralDictionaryVariableMaterialization.compile_slot_exact : ∀ (roles : Yulang.Roles.RoleDecls)
  (state : Yulang.GeneralSourceState.State) (declaration : Yulang.GeneralDeclarations.Declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (name : Nat) (slot : Fin state.slots),
      Yulang.GeneralDictionaryVariableTerms.compile state roles declaration capture name =
          some (Yulang.Core.PresenceGeneration.TyTerm.var slot) ↔
        Yulang.GeneralDictionaryVariableTerms.Denotes roles declaration capture name
          (Yulang.Core.PresenceGeneration.TyTerm.var (state.source slot))
Yulang.GeneralDictionaryVariableMaterialization.compile_variable : ∀ (roles : Yulang.Roles.RoleDecls)
  (state : Yulang.GeneralSourceState.State) (declaration : Yulang.GeneralDeclarations.Declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture) (name : Nat)
  (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
  Yulang.GeneralDictionaryVariableTerms.compile state roles declaration capture name = some term →
    ∃ slot, term = Yulang.Core.PresenceGeneration.TyTerm.var slot
@Yulang.GeneralDictionaryVariableMaterialization.build_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
      (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
      Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located ↔
        Yulang.GeneralDictionaryVariableMaterialization.Materializes declaration capture inputs located
@Yulang.GeneralDictionaryVariableMaterialization.build_none_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand),
      Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = none ↔
        ∀ (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
          ¬Yulang.GeneralDictionaryVariableMaterialization.Materializes declaration capture inputs located
@Yulang.GeneralDictionaryVariableMaterialization.plan_lookup_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryVariablePlans.Result state root),
  Yulang.GeneralDictionaryVariablePlans.lookup registry checked frame root key inputs = some result ↔
    ∃ declaration present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          Yulang.GeneralDictionaryVariableMaterialization.Materializes declaration (frame.capture declaration.id) inputs
              result.located ∧
            result.children = Yulang.GeneralDictionaryEmissionPlans.children frame root declaration ⋯
@Yulang.GeneralDictionaryVariableOrder.bodyTerm_reorders : ∀ {first last : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture) (body : Yulang.GeneralDictionaryAssociatedProvenance.Body),
      Yulang.GeneralDictionaryVariableTerms.bodyTerm first capture body =
        Yulang.GeneralDictionaryVariableTerms.bodyTerm last capture body
@Yulang.GeneralDictionaryVariableOrder.term_lookup_reorders : ∀ {first last : Yulang.GeneralDeclarations.Declaration}
  (roles : Yulang.Roles.RoleDecls),
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture) (name : Nat),
      Yulang.GeneralDictionaryVariableTerms.lookup roles first capture name =
        Yulang.GeneralDictionaryVariableTerms.lookup roles last capture name
@Yulang.GeneralDictionaryVariableOrder.compile_reorders : ∀ {first last : Yulang.GeneralDeclarations.Declaration}
  (roles : Yulang.Roles.RoleDecls) (state : Yulang.GeneralSourceState.State),
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture) (name : Nat),
      Yulang.GeneralDictionaryVariableTerms.compile state roles first capture name =
        Yulang.GeneralDictionaryVariableTerms.compile state roles last capture name
@Yulang.GeneralDictionaryVariableOrder.build_reorders : ∀ {state : Yulang.GeneralSourceState.State}
  {first last : Yulang.GeneralDeclarations.Declaration} {roles : Yulang.Roles.RoleDecls}
  {demand : Yulang.GeneralSourceState.Demand roles},
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture)
      (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand),
      Yulang.GeneralDictionaryVariableTerms.build first capture inputs =
        Yulang.GeneralDictionaryVariableTerms.build last capture inputs
@Yulang.GeneralDictionaryVariableOrder.lookup_reorders_forward : ∀ {state : Yulang.GeneralSourceState.State}
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frame : Yulang.GeneralDictionaryEmissionPlans.Frame roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
      (result : Yulang.GeneralDictionaryVariablePlans.Result state root),
      Yulang.GeneralDictionaryVariablePlans.lookup
            { constructors := constructors, roles := roles, declarations := first } one frame root key inputs =
          some result →
        Yulang.GeneralDictionaryVariablePlans.lookup
            { constructors := constructors, roles := roles, declarations := last } two frame root key inputs =
          some result
@Yulang.GeneralDictionaryVariableOrder.lookup_reorders : ∀ {state : Yulang.GeneralSourceState.State}
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frame : Yulang.GeneralDictionaryEmissionPlans.Frame roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand),
      Yulang.GeneralDictionaryVariablePlans.lookup
          { constructors := constructors, roles := roles, declarations := first } one frame root key inputs =
        Yulang.GeneralDictionaryVariablePlans.lookup
          { constructors := constructors, roles := roles, declarations := last } two frame root key inputs
@Yulang.GeneralDictionaryVariablePlans.lookup_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryVariablePlans.Result state root),
  Yulang.GeneralDictionaryVariablePlans.lookup registry checked frame root key inputs = some result ↔
    ∃ declaration present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          Yulang.GeneralDictionaryVariableTerms.build declaration (frame.capture declaration.id) inputs =
              some result.located ∧
            result.children = Yulang.GeneralDictionaryEmissionPlans.children frame root declaration ⋯
@Yulang.GeneralDictionaryVariablePlans.build_head : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
  Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located → located.head = inputs.head
@Yulang.GeneralDictionaryVariablePlans.lookup_plan : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryVariablePlans.Result state root),
  Yulang.GeneralDictionaryVariablePlans.lookup registry checked frame root key inputs = some result →
    Yulang.GeneralDictionaryEmissionPlans.Plan registry checked frame root key result.children
@Yulang.GeneralDictionaryVariablePlans.lookup_terms : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryVariablePlans.Result state root),
  Yulang.GeneralDictionaryVariablePlans.lookup registry checked (frames root) root key inputs = some result →
    (∀ (declaration : Yulang.GeneralDeclarations.Declaration),
        declaration ∈ registry.declarations →
          declaration.id = key →
            declaration.role = root.demand.role →
              heads root declaration ((frames root).capture declaration.id) inputs.head) →
      Yulang.GeneralDictionaryVariablePlans.Terms registry frames heads root key result.located
@Yulang.GeneralDictionaryVariablePlans.lookup_output_plan : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (result : Yulang.GeneralDictionaryVariablePlans.Result state root),
  Yulang.GeneralDictionaryVariablePlans.lookup registry checked frame root key inputs = some result →
    ∃ declaration _present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          Yulang.GeneralDictionaryPlannedOutputs.OutputPlan registry checked frame root key
              (result.children,
                Yulang.GeneralDictionaryAssociatedProvenance.outputs registry.roles declaration root.demand) ∧
            Yulang.GeneralDictionaryVariableTerms.Interpreted declaration (frame.capture declaration.id) result.located
@Yulang.GeneralDictionaryVariablePreparation.prepare_node_exact : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state root.demand)
  (children : List (Yulang.GeneralDictionaryVariablePreparation.Recipe registry.roles state))
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryVariablePreparation.prepare registry checked frames
        (Yulang.GeneralDictionaryVariablePreparation.Recipe.node root key inputs children) =
      some tree ↔
    ∃ result,
      Yulang.GeneralDictionaryVariablePlans.lookup registry checked (frames root) root key inputs = some result ∧
        ∃ prepared,
          List.mapM (Yulang.GeneralDictionaryVariablePreparation.prepare registry checked frames) children =
              some prepared ∧
            List.map Yulang.GeneralDictionaryTransactions.Prepared.root prepared = result.children ∧
              tree = Yulang.GeneralDictionaryTransactions.Prepared.node root key result.located prepared
@Yulang.GeneralDictionaryVariablePreparation.prepare_root : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (recipe : Yulang.GeneralDictionaryVariablePreparation.Recipe registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryVariablePreparation.prepare registry checked frames recipe = some tree →
    tree.root = recipe.root
@Yulang.GeneralDictionaryVariablePreparation.prepare_built : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (recipe : Yulang.GeneralDictionaryVariablePreparation.Recipe registry.roles state),
  Yulang.GeneralDictionaryVariablePreparation.Heads registry frames heads recipe →
    ∀ (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
      Yulang.GeneralDictionaryVariablePreparation.prepare registry checked frames recipe = some tree →
        Yulang.GeneralDictionaryVariableTransactions.Built registry checked frames heads tree
@Yulang.GeneralDictionaryVariablePreparation.prepare_uniform : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (recipe : Yulang.GeneralDictionaryVariablePreparation.Recipe registry.roles state),
  Yulang.GeneralDictionaryVariablePreparation.Heads registry frames heads recipe →
    ∀ (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
      Yulang.GeneralDictionaryVariablePreparation.prepare registry checked frames recipe = some tree →
        ∃ witness,
          Yulang.GeneralSourceDictionaries.Readback recipe.root (Yulang.GeneralSourceDictionaries.erase tree.dictionary)
              witness ∧
            ∀ (assignment : Yulang.GeneralSourceState.Assignment),
              Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryBatchRecording.record tree.items) assignment →
                Yulang.GeneralSourceDictionaries.Evidence
                  (Yulang.GeneralDictionaryVariableTransactions.SourceInstance registry checked frames heads assignment)
                  witness
Yulang.GeneralDictionaryVariableRealization.singleton_value : ∀ (capture : Yulang.GeneralDeclarationDemands.Capture)
  (assignment : Yulang.GeneralSourceState.Assignment) (binder : Nat) (value : Yulang.Common.Ty),
  (capture.inputs binder).fst = (capture.inputs binder).snd →
    Yulang.Common.Subtype (assignment (capture.inputs binder).fst).fst value ∧
        Yulang.Common.Subtype value (assignment (capture.inputs binder).snd).fst →
      Yulang.Common.Equivalent value (assignment (capture.inputs binder).fst).fst
Yulang.GeneralDictionaryVariableRealization.denotes_realization : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (assignment : Yulang.GeneralSourceState.Assignment) (values : Nat → Yulang.Common.Ty),
  Yulang.GeneralDictionaryVariableRealization.Realizes declaration capture assignment values →
    ∀ (name : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm Nat),
      Yulang.GeneralDictionaryVariableTerms.Denotes roles declaration capture name term →
        ∃ equation binder,
          Yulang.GeneralDictionaryAssociatedProvenance.Supplies roles declaration name
              (Yulang.GeneralDictionaryAssociatedProvenance.Body.explicit equation) ∧
            Yulang.GeneralDeclarationPatterns.normalize equation.rhs =
                Yulang.GeneralDeclarationPatterns.Pattern.var binder ∧
              Yulang.Common.Equivalent (values binder)
                (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment term)
@Yulang.GeneralDictionaryVariableRealization.built_output_realization : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
      (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
      Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located →
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryEquationRecording.record located) assignment →
            ∀ (values : Nat → Yulang.Common.Ty),
              Yulang.GeneralDictionaryVariableRealization.Realizes declaration capture assignment values →
                ∀ (index : Fin demand.outputs.length),
                  ∃ equation binder,
                    Yulang.GeneralDictionaryAssociatedProvenance.Supplies roles declaration demand.outputs[index].name
                        (Yulang.GeneralDictionaryAssociatedProvenance.Body.explicit equation) ∧
                      Yulang.GeneralDeclarationPatterns.normalize equation.rhs =
                          Yulang.GeneralDeclarationPatterns.Pattern.var binder ∧
                        Yulang.Common.Equivalent (assignment demand.outputs[index].target).fst (values binder)
Yulang.GeneralDictionaryVariableTerms.lookup_exact : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (name : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm Nat),
      Yulang.GeneralDictionaryVariableTerms.lookup roles declaration capture name = some term ↔
        Yulang.GeneralDictionaryVariableTerms.Denotes roles declaration capture name term
Yulang.GeneralDictionaryVariableTerms.output_lookup_preserved : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (name : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm Nat),
      Yulang.GeneralDictionaryOutputBinderTerms.lookup roles declaration capture name = some term →
        Yulang.GeneralDictionaryVariableTerms.lookup roles declaration capture name = some term
Yulang.GeneralDictionaryVariableTerms.compile_interpreted : ∀ (state : Yulang.GeneralSourceState.State)
  (roles : Yulang.Roles.RoleDecls) (declaration : Yulang.GeneralDeclarations.Declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture) (name : Nat)
  (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
  Yulang.GeneralDictionaryVariableTerms.compile state roles declaration capture name = some term →
    Yulang.GeneralDictionaryVariableTerms.lookup roles declaration capture name =
      some (Yulang.GeneralDictionaryStateEquations.liftType state term)
@Yulang.GeneralDictionaryVariableTerms.build_interpreted : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
  Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located →
    Yulang.GeneralDictionaryVariableTerms.Interpreted declaration capture located
@Yulang.GeneralDictionaryVariableTerms.build_head : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
  Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located → located.head = inputs.head
@Yulang.GeneralDictionaryVariableTerms.build_output_denotes : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
      (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
      Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located →
        ∀ (index : Fin demand.outputs.length),
          Yulang.GeneralDictionaryVariableTerms.Denotes roles declaration capture demand.outputs[index].name
            (located.equations.output index)
@Yulang.GeneralDictionaryVariableTerms.built_output_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
      (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
      Yulang.GeneralDictionaryVariableTerms.build declaration capture inputs = some located →
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryEquationRecording.record located) assignment →
            ∀ (index : Fin demand.outputs.length),
              Yulang.GeneralDictionaryVariableTerms.Denotes roles declaration capture demand.outputs[index].name
                  (located.equations.output index) ∧
                Yulang.Common.Equivalent (assignment demand.outputs[index].target).fst
                  (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment
                    (located.equations.output index))
@Yulang.GeneralDictionaryVariableTransactions.built_valid : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryVariableTransactions.Built registry checked frames heads tree →
    Yulang.GeneralDictionaryTransactions.Valid registry checked frames
      (Yulang.GeneralDictionaryVariablePlans.Terms registry frames heads) tree
@Yulang.GeneralDictionaryVariableTransactions.transaction_stored : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryVariableTransactions.Built registry checked frames heads tree →
    Yulang.GeneralSourceDictionaries.Evidence
      (Yulang.GeneralDictionaryModelEvidence.StoredInstance
        (Yulang.GeneralDictionaryTransactions.PlannedAt registry checked frames
          (Yulang.GeneralDictionaryTransactions.LiftedTerms tree.items
            (Yulang.GeneralDictionaryVariablePlans.Terms registry frames heads))))
      tree.dictionary
@Yulang.GeneralDictionaryVariableTransactions.lifted_source_instance : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (items : List (Yulang.GeneralDictionaryBatchRecording.Item registry.roles state))
  (assignment : Yulang.GeneralSourceState.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralDictionaryModelEvidence.ModelInstance
      (Yulang.GeneralDictionaryTransactions.PlannedAt registry checked frames
        (Yulang.GeneralDictionaryTransactions.LiftedTerms items
          (Yulang.GeneralDictionaryVariablePlans.Terms registry frames heads)))
      assignment root key children →
    Yulang.GeneralDictionaryVariableTransactions.SourceInstance registry checked frames heads assignment root key
      children
@Yulang.GeneralDictionaryVariableTransactions.transaction_uniform : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  Yulang.GeneralDictionaryVariableTransactions.Built registry checked frames heads tree →
    ∃ witness,
      Yulang.GeneralSourceDictionaries.Readback tree.root (Yulang.GeneralSourceDictionaries.erase tree.dictionary)
          witness ∧
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryBatchRecording.record tree.items) assignment →
            Yulang.GeneralSourceDictionaries.Evidence
              (Yulang.GeneralDictionaryVariableTransactions.SourceInstance registry checked frames heads assignment)
              witness
@Yulang.GeneralDictionaryVariableTransactions.source_instance_declaration : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (assignment : Yulang.GeneralSourceState.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralDictionaryVariableTransactions.SourceInstance registry checked frames heads assignment root key
      children →
    ∃ declaration present,
      declaration.id = key ∧
        declaration.role = root.demand.role ∧
          children = Yulang.GeneralDictionaryEmissionPlans.children (frames root) root declaration ⋯ ∧
            ∃ located,
              heads root declaration ((frames root).capture declaration.id) located.head ∧
                Yulang.GeneralDictionaryVariableTerms.Interpreted declaration ((frames root).capture declaration.id)
                    located ∧
                  located.equations.Holds assignment
@Yulang.GeneralDictionaryVariableTransactions.source_output_denotes : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (heads : Yulang.GeneralDictionaryVariablePlans.HeadInstances registry.roles state)
  (assignment : Yulang.GeneralSourceState.Assignment)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Yulang.GeneralDictionaryVariableTransactions.SourceInstance registry checked frames heads assignment root key
      children →
    ∀ (index : Fin root.demand.outputs.length),
      ∃ declaration present,
        declaration.id = key ∧
          declaration.role = root.demand.role ∧
            children = Yulang.GeneralDictionaryEmissionPlans.children (frames root) root declaration ⋯ ∧
              ∃ term,
                Yulang.GeneralDictionaryVariableTerms.Denotes registry.roles declaration
                    ((frames root).capture declaration.id) root.demand.outputs[index].name term ∧
                  Yulang.Common.Equivalent (assignment root.demand.outputs[index].target).fst
                    (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment term)
Yulang.GeneralDictionaryVariableHeads.compileAt_exact : ∀ (state : Yulang.GeneralSourceState.State)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (index : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
  Yulang.GeneralDictionaryVariableHeads.compileAt state declaration capture index = some term ↔
    Yulang.GeneralDictionaryVariableHeads.DenotesAt state declaration capture index term
@Yulang.GeneralDictionaryVariableHeads.build_head_denotes : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration)
  (sameRole : declaration.role = demand.role) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state demand)
  (result : Yulang.GeneralDictionaryBinderLocations.Inputs state demand),
  Yulang.GeneralDictionaryVariableHeads.build declaration checked sameRole capture inputs = some result →
    Yulang.GeneralDictionaryVariableHeads.HeadDenotes declaration capture demand result.head
@Yulang.GeneralDictionaryVariableHeads.build_preserves : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration)
  (sameRole : declaration.role = demand.role) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state demand)
  (result : Yulang.GeneralDictionaryBinderLocations.Inputs state demand),
  Yulang.GeneralDictionaryVariableHeads.build declaration checked sameRole capture inputs = some result →
    result.lower = inputs.lower ∧ result.upper = inputs.upper ∧ result.target = inputs.target
@Yulang.GeneralDictionaryVariableHeads.build_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration)
  (sameRole : declaration.role = demand.role) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs state demand)
  (result : Yulang.GeneralDictionaryBinderLocations.Inputs state demand),
  Yulang.GeneralDictionaryVariableHeads.build declaration checked sameRole capture inputs = some result ↔
    result.lower = inputs.lower ∧
      result.upper = inputs.upper ∧
        result.target = inputs.target ∧
          Yulang.GeneralDictionaryVariableHeads.HeadDenotes declaration capture demand result.head
@Yulang.GeneralDictionaryVariableHeads.denotesAt_realization : ∀ {state : Yulang.GeneralSourceState.State}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (assignment : Yulang.GeneralSourceState.Assignment) (values : Nat → Yulang.Common.Ty),
  Yulang.GeneralDictionaryVariableRealization.Realizes declaration capture assignment values →
    ∀ (index : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
      Yulang.GeneralDictionaryVariableHeads.DenotesAt state declaration capture index term →
        ∃ pattern binder,
          declaration.head[index]? = some pattern ∧
            Yulang.GeneralDeclarationPatterns.normalize pattern = Yulang.GeneralDeclarationPatterns.Pattern.var binder ∧
              Yulang.Common.Equivalent (values binder)
                (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment
                  (Yulang.GeneralDictionaryStateEquations.liftType state term))
Yulang.GeneralDictionaryHeadExamples.leaf_positional_compiles : Yulang.GeneralDictionaryVariableHeads.compileAt
    Yulang.GeneralDictionaryTerminalFixture.state Yulang.GeneralDictionaryTerminalFixture.leaf
    Yulang.GeneralDictionaryTerminalFixture.capture 0 =
  some (Yulang.Core.PresenceGeneration.TyTerm.var 0)
Yulang.GeneralDictionaryHeadExamples.leaf_head_denotes : Yulang.GeneralDictionaryVariableHeads.HeadDenotes
  Yulang.GeneralDictionaryTerminalFixture.leaf Yulang.GeneralDictionaryTerminalFixture.capture
  Yulang.GeneralDictionaryTerminalFixture.childDemand Yulang.GeneralDictionaryTerminalFixture.childInputs.head
Yulang.GeneralDictionaryHeadExamples.leaf_head_builds : Yulang.GeneralDictionaryVariableHeads.build
    Yulang.GeneralDictionaryTerminalFixture.leaf Yulang.GeneralDictionaryTerminalFixture.leaf_checked ⋯
    Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryHeadExamples.childHeadless =
  some Yulang.GeneralDictionaryTerminalFixture.childInputs
Yulang.GeneralDictionaryHeadExamples.leaf_concrete_head : Yulang.GeneralDictionaryVariableHeads.heads
  Yulang.GeneralDictionaryTerminalFixture.registry.roles Yulang.GeneralDictionaryTerminalFixture.state
  Yulang.GeneralDictionaryTerminalFixture.child Yulang.GeneralDictionaryTerminalFixture.leaf
  Yulang.GeneralDictionaryTerminalFixture.capture Yulang.GeneralDictionaryTerminalFixture.childInputs.head
Yulang.GeneralDictionaryHeadExamples.nominal_root_defers : Yulang.GeneralDictionaryVariableHeads.build
    Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
    Yulang.GeneralDictionaryOutputBinderExamples.binderWrap_checked ⋯ Yulang.GeneralDictionaryTerminalFixture.capture
    Yulang.GeneralDictionaryHeadExamples.rootHeadless =
  none
Yulang.GeneralDictionaryHeadExamples.unequal_leaf_defers : Yulang.GeneralDictionaryVariableHeads.build
    Yulang.GeneralDictionaryTerminalFixture.leaf Yulang.GeneralDictionaryTerminalFixture.leaf_checked ⋯
    Yulang.GeneralDictionaryHeadExamples.unequalCapture Yulang.GeneralDictionaryHeadExamples.childHeadless =
  none
Yulang.GeneralDictionaryHeadExamples.absent_source_defers : Yulang.GeneralDictionaryVariableHeads.build
    Yulang.GeneralDictionaryTerminalFixture.leaf Yulang.GeneralDictionaryTerminalFixture.leaf_checked ⋯
    Yulang.GeneralDictionaryHeadExamples.absentCapture Yulang.GeneralDictionaryHeadExamples.childHeadless =
  none
```

## Runtime case interpretation

Runtime.lean evaluates these cases in order: complete two-level recipe; root missing its required child; root with an extra duplicate child; absent declaration key 99; terminal leaf with unequal captured input endpoints. The recorded [true, false, false, false, false] is exactly that order. Failure means preparation deferred, not semantic language rejection.

Runtime source, complete:

```lean
import Yulang.GeneralDictionaryPreparationExamples
open Yulang.GeneralDictionaryTerminalFixture
open Yulang.GeneralDictionaryVariablePreparation
open Yulang.GeneralDictionaryPreparationExamples
#eval [(prepare registry registry_checked (fun _ => frame) recipe).isSome,
 (prepare registry registry_checked (fun _ => frame) (.node root 2 rootInputs [])).isSome,
 (prepare registry registry_checked (fun _ => frame) (.node root 2 rootInputs [childRecipe,childRecipe])).isSome,
 (prepare registry registry_checked (fun _ => frame) (.node root 99 rootInputs [childRecipe])).isSome,
 (prepare registry registry_checked (fun _ => unequalFrame) childRecipe).isSome]
```

## Earlier attempts: failures are not successes

- plans-build: exit 1. An unused `present` variable warning failed the warnings-as-errors build.
- plans-build2: exit 1. A binder rename introduced a membership-proof type mismatch, followed by unavailable lookup_exact errors. plans-build3 subsequently passed.
- materialization-build: exit 1. The identifier `matches` was parsed as a reserved token, leaving a proof goal. materialization-build2 subsequently passed.
- preparation-build: exit 1. Added integration references used nonexistent GeneralDictionaryReadback.Readback/Evidence names. preparation-build2 subsequently passed.
- final-gate-dirty: explicit FAIL because lean/ contained modified/untracked files before the final commit. No separate exit-status file is retained for this attempt. The post-commit final-gate log is a distinct successful run.
- final-signatures-failed: explicit Unknown option pp.width error. No separate failed-run exit-status file is retained. The unsupported option was removed, and the corrected final-signatures run exited 0. The failed log must not be interpreted as successful signature verification.

### plans-build

Stored exit status: 1

Captured combined stdout/stderr, complete:

```text
⚠ [534/534] Building Yulang.GeneralDictionaryComputedOutputPlans (11s)
trace: .> LEAN_PATH=/workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean /workspace/scratch/1d0b4aaa3394/cache/toolchain116/lean-4.35.0-linux/bin/lean --trust=0 /workspace/scratch/1d0b4aaa3394/yulang/lean/Yulang/GeneralDictionaryComputedOutputPlans.lean -o /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryComputedOutputPlans.olean -i /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryComputedOutputPlans.ilean -c /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryComputedOutputPlans.c --setup /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryComputedOutputPlans.setup.json --json
warning: Yulang/GeneralDictionaryComputedOutputPlans.lean:131:21: Variable name `present` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _present

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Some required targets logged failures:
- Yulang.GeneralDictionaryComputedOutputPlans
error: build failed
```

### plans-build2

Stored exit status: 1

Captured combined stdout/stderr, complete:

```text
✖ [534/534] Building Yulang.GeneralDictionaryComputedOutputPlans (44s)
trace: .> LEAN_PATH=/workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean /workspace/scratch/1d0b4aaa3394/cache/toolchain116/lean-4.35.0-linux/bin/lean --trust=0 /workspace/scratch/1d0b4aaa3394/yulang/lean/Yulang/GeneralDictionaryComputedOutputPlans.lean -o /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryComputedOutputPlans.olean -i /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryComputedOutputPlans.ilean -c /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryComputedOutputPlans.c --setup /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryComputedOutputPlans.setup.json --json
error: Yulang/GeneralDictionaryComputedOutputPlans.lean:61:81: Application type mismatch: The argument
  present
has type
  ?m.1
but is expected to have type
  declaration ∈ registry.declarations
in the application
  checked.right declaration present
error: Yulang/GeneralDictionaryComputedOutputPlans.lean:104:5: Unknown identifier `lookup_exact`
error: Yulang/GeneralDictionaryComputedOutputPlans.lean:103:9: Tactic `rcases` failed: `x✝ : ?m.11` is not an inductive datatype
error: Yulang/GeneralDictionaryComputedOutputPlans.lean:119:5: Unknown identifier `lookup_exact`
error: Yulang/GeneralDictionaryComputedOutputPlans.lean:118:9: Tactic `rcases` failed: `x✝ : ?m.24` is not an inductive datatype
error: Yulang/GeneralDictionaryComputedOutputPlans.lean:137:5: Unknown identifier `lookup_exact`
error: Yulang/GeneralDictionaryComputedOutputPlans.lean:136:9: Tactic `rcases` failed: `x✝ : ?m.31` is not an inductive datatype
Some required targets logged failures:
- Yulang.GeneralDictionaryComputedOutputPlans
error: build failed
```

### materialization-build

Stored exit status: 1

Captured combined stdout/stderr, complete:

```text
✖ [536/536] Building Yulang.GeneralDictionaryVariableMaterialization (3.1s)
trace: .> LEAN_PATH=/workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean /workspace/scratch/1d0b4aaa3394/cache/toolchain116/lean-4.35.0-linux/bin/lean --trust=0 /workspace/scratch/1d0b4aaa3394/yulang/lean/Yulang/GeneralDictionaryVariableMaterialization.lean -o /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryVariableMaterialization.olean -i /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryVariableMaterialization.ilean -c /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryVariableMaterialization.c --setup /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryVariableMaterialization.setup.json --json
error: Yulang/GeneralDictionaryVariableMaterialization.lean:91:12: unexpected token 'matches'; expected '⟩'
error: Yulang/GeneralDictionaryVariableMaterialization.lean:91:2: unsolved goals
case mpr
roles : Roles.RoleDecls
state : State
demand : Demand roles
declaration : Declaration
capture : Capture
unique : (List.map Equation.name declaration.associated).Nodup
inputs : Inputs state demand
located : Located state demand
left✝ : Matches inputs located
right✝ :
  ∀ (index : Fin demand.outputs.length),
    ∃ slot,
      located.output index = TyTerm.var slot ∧
        Denotes roles declaration capture demand.outputs[index].name (TyTerm.var (state.source slot))
⊢ build declaration capture inputs = some located
Some required targets logged failures:
- Yulang.GeneralDictionaryVariableMaterialization
error: build failed
```

### preparation-build

Stored exit status: 1

Captured combined stdout/stderr, complete:

```text
✖ [537/537] Building Yulang.GeneralDictionaryVariablePreparation (1.8s)
trace: .> LEAN_PATH=/workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean /workspace/scratch/1d0b4aaa3394/cache/toolchain116/lean-4.35.0-linux/bin/lean --trust=0 /workspace/scratch/1d0b4aaa3394/yulang/lean/Yulang/GeneralDictionaryVariablePreparation.lean -o /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryVariablePreparation.olean -i /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryVariablePreparation.ilean -c /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryVariablePreparation.c --setup /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryVariablePreparation.setup.json --json
error: Yulang/GeneralDictionaryVariablePreparation.lean:148:15: Unknown identifier `GeneralDictionaryReadback.Readback`
error: Yulang/GeneralDictionaryVariablePreparation.lean:150:8: Unknown identifier `GeneralDictionaryReadback.Evidence`
Some required targets logged failures:
- Yulang.GeneralDictionaryVariablePreparation
error: build failed
```

### final-gate-dirty

Stored exit status: not separately retained; use the explicit diagnostic below.

Captured combined stdout/stderr, complete:

```text
FAIL: lean/ has uncommitted or untracked files:
 M lean/Audit.lean
 M lean/README.md
 M lean/Yulang.lean
?? lean/Yulang/GeneralDictionaryHeadExamples.lean
?? lean/Yulang/GeneralDictionaryVariableHeads.lean
verify-lean: . @ 31be151e7 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: FAIL
```

### Initial final-signatures failure

The complete failed signature log repeats the long signature inventory and is retained at cache/yulang126/final-signatures-failed.log. Its error line is reproduced verbatim below; complete corrected output is already included above.

```text
../cache/yulang126/FinalSignatures.lean:18:0: error: Unknown option `pp.width`
```

## Earlier stored exit statuses

- boundary-build: 0
- checkpoint-audit: 0
- checkpoint-build: 0
- checkpoint-gate: 0
- compatibility-build: 0
- final-audit: 0
- final-build: 0
- final-diff: 0
- final-gate: 0
- final-signatures: 0
- heads-build: 0
- materialization-build: 1
- materialization-build2: 0
- order-build: 0
- plans-audit: 0
- plans-build: 1
- plans-build2: 1
- plans-build3: 0
- preparation-build: 1
- preparation-build2: 0
- realization-build: 0
- runtime-audit: 0
- runtime: 0
- second-audit: 0
- second-build: 0
- second-gate: 0
- transactions-build: 0
- variables-build: 0

## Earlier successful focused checks and checkpoints

### plans-build3

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
✔ [534/534] Built Yulang.GeneralDictionaryComputedOutputPlans (5.9s)
Build completed successfully (534 jobs).
```

### plans-audit

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.build_head' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_output_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### transactions-build

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
✔ [535/535] Built Yulang.GeneralDictionaryComputedTransactions (13s)
Build completed successfully (535 jobs).
```

### boundary-build

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
✔ [536/536] Built Yulang.GeneralDictionaryBinderOnlyBoundary (57s)
Build completed successfully (536 jobs).
```

### checkpoint-build

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
✔ [539/539] Built Yulang.GeneralDictionaryComputedOutputExamples (12s)
Build completed successfully (539 jobs).
```

### checkpoint-audit

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.build_head' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_output_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.built_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.transaction_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.lifted_source_instance' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.transaction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.source_instance_declaration' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.source_output_denotes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.actual_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.absent_key_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.wrong_role_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.computes_repeated_outputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.retains_distinct_targets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.supplies_complete_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.supplies_concrete_terms' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.same_visible_declaration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_computed_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_repeated_targets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.missing_binder_defers' depends on axioms: [propext, Quot.sound]
```

### checkpoint-gate

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
verify-lean: . @ 359e8a533 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

### variables-build

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
✔ [534/536] Built Yulang.GeneralDictionaryVariableTerms (17s)
✔ [535/536] Built Yulang.GeneralDictionaryVariablePlans (2.9s)
✔ [536/536] Built Yulang.GeneralDictionaryVariableTransactions (8.3s)
Build completed successfully (536 jobs).
```

### materialization-build2

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
✔ [536/536] Built Yulang.GeneralDictionaryVariableMaterialization (28s)
Build completed successfully (536 jobs).
```

### order-build

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
✔ [537/537] Built Yulang.GeneralDictionaryVariableOrder (60s)
Build completed successfully (537 jobs).
```

### compatibility-build

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
✔ [535/536] Built Yulang.GeneralDictionaryVariableExamples (45s)
✔ [536/536] Built Yulang.GeneralDictionaryVariableCompatibility (45s)
Build completed successfully (536 jobs).
```

### second-build

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
✔ [545/547] Built Yulang.GeneralDictionaryVariableCompatibility (54s)
✔ [546/547] Built Yulang.GeneralDictionaryVariableExamples (54s)
✔ [547/547] Built Yulang.GeneralDictionaryTerminalFixture (55s)
Build completed successfully (547 jobs).
```

### second-audit

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.build_head' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputPlans.lookup_output_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.built_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.transaction_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.lifted_source_instance' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.transaction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.source_instance_declaration' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedTransactions.source_output_denotes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.actual_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.absent_key_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.wrong_role_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.computes_repeated_outputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.retains_distinct_targets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.supplies_complete_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.supplies_concrete_terms' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.same_visible_declaration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_computed_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.nonidentity_repeated_targets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryComputedOutputExamples.missing_binder_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBinderOnlyBoundary.output_requires_nonempty_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBinderOnlyBoundary.built_root_outputs_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.output_lookup_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.compile_interpreted' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.build_interpreted' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.build_head' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.build_output_denotes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTerms.built_output_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableCompatibility.compile_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableCompatibility.build_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.singleton_input_lookup' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.unequal_input_deferred' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.output_binder_unchanged' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.compound_deferred' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.default_deferred' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.nonidentity_input_compiles' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableExamples.nonidentity_input_build' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariablePlans.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariablePlans.build_head' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariablePlans.lookup_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariablePlans.lookup_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariablePlans.lookup_output_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTransactions.built_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTransactions.transaction_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTransactions.lifted_source_instance' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTransactions.transaction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTransactions.source_instance_declaration' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTransactions.source_output_denotes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableMaterialization.compile_slot_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableMaterialization.compile_variable' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableMaterialization.build_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableMaterialization.build_none_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableMaterialization.plan_lookup_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableOrder.bodyTerm_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableOrder.term_lookup_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableOrder.compile_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableOrder.build_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableOrder.lookup_reorders_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableOrder.lookup_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.leaf_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.root_actual_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.child_actual_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.root_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.child_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.joint_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.tree_items' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.tree_joint_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.retained_outputs' depends on axioms: [propext]
'Yulang.GeneralDictionaryTerminalFixture.root_build' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.child_build' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.root_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.child_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.tree_built' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.uniform_completion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalFixture.all_model_root_child_input' depends on axioms: [propext, Quot.sound]
```

### second-gate

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
verify-lean: . @ b190215fa (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

### preparation-build2

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
✔ [540/541] Built Yulang.GeneralDictionaryVariablePreparation (12s)
✔ [541/541] Built Yulang.GeneralDictionaryPreparationExamples (2.2s)
Build completed successfully (541 jobs).
```

### realization-build

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
✔ [537/537] Built Yulang.GeneralDictionaryVariableRealization (9.8s)
Build completed successfully (537 jobs).
```

### heads-build

Stored exit status: 0

Captured combined stdout/stderr, complete:

```text
✔ [542/543] Built Yulang.GeneralDictionaryVariableHeads (4.6s)
✔ [543/543] Built Yulang.GeneralDictionaryHeadExamples (1.5s)
Build completed successfully (543 jobs).
```

## Hosted CI と公開sourceの検証

以下はGitHub job logsから確認した結果であり、local全体buildの実行記録ではない。

| source | core / proof | full build | 新定理全件 | 全tree |
| --- | --- | --- | --- | --- |
| d8892fd9bed56ec6330170ae7e05ab5c5696bca1 | success / success | 1381 jobs | 24 / 24 | 2418 files一致 |
| 22b5de4e84852c0ac5f54903c36455d200dcc383 | success / success | 1390 jobs | 81 / 81 | 2427 files一致 |
| cb899edd91b7d414202886b2c1b9c6e3095dceec | success / success | 1395 jobs | 109 / 109 | 2432 files一致 |

最終 [core](https://github.com/momota1029/yulang/actions/runs/43108794096/job/130819016760) / [proof](https://github.com/momota1029/yulang/actions/runs/43108794068/job/130819016872)。

最終proof logのcheckout/build/audit command抜粋:

```text
2026-11-11T22:05:46.8359284Z [command]/usr/bin/git log -1 --format=%H
2026-11-11T22:05:46.8379550Z cb899edd91b7d414202886b2c1b9c6e3095dceec
2026-11-11T22:06:10.3482120Z Build completed successfully (1395 jobs).
2026-11-11T22:06:14.6055183Z ##[group]Run lake env lean --trust=0 Audit.lean
```

公理抽出は行頭のISO timestampを除去した後に複数行の `depends on axioms: [...]` を連結。
8550依存出力、今回の109名の不足0、全体の許可外公理0。許可集合は
`Classical.choice, Quot.sound, propext`。scoped109件の全文は上記local auditにもある。
最終treeは `d4720a64140f622716de5b55276f5296c1b72f0f`。
remote recursive treeのtruncated=false、各path/mode/type/blob SHAをlocal tree全2432件と比較し一致。

## 報告公開後の最終整合検査（22:13UTC）

同じsourceについて、報告追加後のcommit fcee0fe9dでdiff-only gateとgit diff --checkを再実行。
ともにexit0。新しいLean sourceは追加していない。

```text
verify-lean: . @ fcee0fe9d (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

integrationからの新module17件からpublic theorem名を再抽出し109件。
final-namesと完全一致、Audit登録不足0、Yulang集約import不足0、定理報告109項目。
report treeの2435 tracked files（3報告を含む）もlocalとremoteのpath/mode/type/blob SHAが
全件一致し、truncated=falseだった。source以後の差分は報告3つとheartbeatだけである。
