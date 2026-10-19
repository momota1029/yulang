# R102 implementation/source API audit

Status: FROZEN WITH EXACT OWNER BLOCKER
Contract: `tasks/agent-loop/sprints/r101-source-entry-completion-20261019-r102.md`
Contract SHA-256: `6c6a5fda1b142df6356fe90d16f08c4b7180f9d694fdaeea3ea6c8088af16ced`

## Pin receipts

Every opened pin matched its rev3 SHA-256, including the R101 contract, proof, and test; the HIR module, source annotation, local source, and source identity owners; candidate source and shadow apply; and runtime literal, program, machine, and receiving owners. No pin mismatch was observed.

## Frozen test route established by static inspection

The test imports and calls these APIs directly (`tools/inference-playground/tests/runtime_handler_priority.rs`):

1. `SourceText`, `scan_header`, `SyntaxEnvironment::empty`, and `parse_file` form the parsed input. It asserts an empty syntax-diagnostic list before lowering.
2. `lower_module_with_local_source` receives that parsed file and a source-root module identity. Its pinned owner (`crates/yu-hir/src/module.rs`) creates `HirSourceIdentity`, source keys, sets the local-source lowering mode, and calls `lower_module_with_counters`. The per-source-root LocalSource storage and constructors are owned by the pinned `module/local_source.rs`; source effect declarations and annotation formation are delegated to pinned `module/source_annotation.rs`.
3. `CandidateInference::solve(hir.clone())` is called, followed by `candidate.candidate_conflicts().is_empty()`. The pinned solver routes `solve` to `solve_mode(hir, false, false)`; `candidate_conflicts` exposes the stored solver errors. Its source owner explicitly says candidate conflicts never establish source rejection. This test check is a candidate consistency assertion, not a principal-inference or runtime-execution certificate.
4. The test collects `(spelling, SourceOperationId)` from `hir.source_effect_declarations().operations`. The pinned runtime program lowers each `LocalSourceForm::Operation` resolution into an `Instruction::Operation`, preserving the resolved source operation declaration/ID. In the third cell the runtime outcome's `operation` is compared with the ID selected from the HIR declaration inventory by spelling `tick`.
5. `RuntimeProgram::from_hir(hir, RuntimeEvidence::default())` constructs the runtime program from HIR-owned roots and LocalSource. It is passed no CandidateInference and no evidence derived from the preceding candidate check. The test selects `main` through `definition_named`, gets `execution_roots`, and calls public `start(selected, &roots)`.
6. `Machine::run(10_000)` returns either a terminal outcome or `ResourceExhausted`; the test requires `Completed` for the first two cells and `UnhandledRequest` for the third. The integer payload/result is read as `RuntimeValueKind::Integer` and compared textually. The pinned `literal::integer` accepts ASCII decimal digits and canonicalizes leading zeroes without a machine-width bound; machine evaluation invokes it when evaluating an integer instruction.
7. The request outcome's `SourceSite` carries source-root identity, HIR occurrence, and byte range. Program construction fills it from each LocalSource expression's source root, occurrence, and range. Operation payload evaluation creates a request carrier with that site; execution returns `PendingRequest` with the carrier's preserved source; an unmatched request becomes `RuntimeOutcome::UnhandledRequest` with that source. Thus the test's `source.range` assertion observes the runtime-carried request site. Whether the exact source parser/lowering creates the expected `::tick 11` range is a source-construction premise for the proof lane and remains unobserved until the authorized command.

## Exact missing owner / stop

The pinned `RuntimeProgram::from_hir` calls `super::primitive::closed_primitive(&program)` (`tools/inference-playground/src/runtime/program.rs`, `closed_primitive` assignment). The machine's request-selection path branches on `program.closed_primitive` before requiring a positive receiving-local grant (`tools/inference-playground/src/runtime/machine.rs`, handler request path). The implementation of that predicate is a required owner for deciding which handler-admission branch these exact `act io` fixtures take. It is outside the rev3 frozen inputs. Per the contract, I stopped without opening it or inferring its behavior.

Exact blocker to add in a new contract revision: `tools/inference-playground/src/runtime/primitive.rs` (the owner reached as `super::primitive::closed_primitive`; exact path inferred from the pinned module reference, file not opened). No runtime success, shallow-selection behavior, or expected source range is established by this static audit. The single authorized command remains the only allowed first observation after all audits/reviews are CLEAN.

## Evidence limits

This audit establishes the frozen test's call graph, evidence flow, source-ID comparison, literal decoding path, and request-site carrier path by source inspection only. It did not execute a test, build, compiler, runtime, formatter, CLI, or Git command. It does not establish parse success for the three source strings, empty candidate conflicts, runtime construction success, branch selection, completion values, request payload, or exact source-range observation. It does not close the R101 source-entry premise or any parent effect-hygiene, Simple-sub, evaluator, method/role, adoption, or production gate.

## New paths and scratch

Only this leased handoff was written: `tasks/agent-loop/inbox/20261019-r102-implementation.md`. No generated or disposable scratch paths were created.
