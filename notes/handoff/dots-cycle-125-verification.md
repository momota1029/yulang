# Cycle125: verification evidence

No local full build, full Audit, or supervisor AxiomGate was run.

Commands:

```sh
cd lean
lake build Yulang.GeneralDictionaryOutputBinderTerms Yulang.GeneralDictionaryBinderLocations Yulang.GeneralDictionaryOutputBinderExamples Yulang.GeneralDictionaryBinderLocationExamples --wfail
lake env lean --trust=0 -j1 ../cache/yulang125/FinalAudit.lean
lake env lean --trust=0 -j1 ../cache/yulang125/FinalSignatures.lean
cd ..
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
git diff --check
```

## Final focused build (all four modules), exit0

```text
✔ [532/533] Built Yulang.GeneralDictionaryBinderLocations (9.8s)
✔ [533/533] Built Yulang.GeneralDictionaryBinderLocationExamples (1.9s)
Build completed successfully (533 jobs).
```

## Final scoped trust-zero axiom audit,39 declarations, exit0

```text
'Yulang.GeneralDictionaryOutputBinderTerms.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputBinderTerms.denotes_functional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputBinderTerms.denotes_has_producer' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputBinderTerms.outputs_sources' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputBinderTerms.recorded_output_denotes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputBinderTerms.recorded_output_producer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBinderLocations.sourceSlot_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBinderLocations.locateTerm_lifts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBinderLocations.compile_interpreted' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBinderLocations.compile_source_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBinderLocations.compile_slot_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBinderLocations.build_interpreted' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBinderLocations.built_output_denotes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.binderWrap_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.actual_rhs_lookup' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.actual_rhs_denotes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.child_producer_target' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.compound_deferred' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.input_deferred' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.positional_default_retained' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.default_deferred' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.repeated_root_targets' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.located_interpreted' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.recording_has_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.all_model_binder_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.all_model_child_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.all_model_actual_producer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputBinderExamples.repeated_equations_recorded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBinderLocationExamples.prior_source_lookup' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBinderLocationExamples.prior_rhs_compiles' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBinderLocationExamples.reconstructs_prior_located' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBinderLocationExamples.nonidentity_source_lookup' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBinderLocationExamples.nonidentity_rhs_compiles' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBinderLocationExamples.nonidentity_lift_returns_actual_source' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryBinderLocationExamples.builds_nonidentity_locations' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBinderLocationExamples.success_preserves_repeated_targets' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryBinderLocationExamples.missing_binder_source_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBinderLocationExamples.compound_defers_entire_build' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBinderLocationExamples.input_defers_entire_build' depends on axioms: [propext, Quot.sound]
```

## Final no-build gate, exit0

```text
verify-lean: . @ 01c287a78 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

## Bounded failures and recovery

Several project-import-only and focused attempts returned timeout124 with no
diagnostics. A minimal Nat check succeeded, and a project import probe reproduced
the delay independently. The exact cause is not established. No timeout counts as
a pass. The first source-slot attempt had an unknown simplification name and a
record-layout parse error. The first combined regression check had three proof
errors (two Option.get reductions and a source-map injectivity proof). These were
fixed without changing the expected behavior. Combined check then passed37 public
axiom outputs; the two subsequent general completeness lemmas were verified in
the final533-job build and final39-declaration audit above.

The changed four source modules and their exact imported versions passed the
final focused build. No earlier failed proof, generated placeholder, timeout, or
partial audit is included in the reported success.

## Exact final hosted source

Commit: `4f7210f07e000b71c036427746a684306d9ca8fd`.
Verified checkout SHA, successful full1378-job build, full Audit containing all39
new public declarations, permitted axioms only. Core and proof both succeeded.
Job: https://github.com/momota1029/yulang/actions/runs/43101133893/job/130792592923
The first source checkpoint also passed full1375-job hosted proof/core; it is
not being substituted for the final source check. Supervisor AxiomGate was not run.
