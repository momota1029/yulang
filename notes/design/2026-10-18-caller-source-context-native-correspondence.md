# R29 source/native correspondence: caller source-context action

Status: research correspondence audit; no implementation, tests or semantic
proof. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains
OPEN/closure0, original scope unchanged. R29's adopted pure source-context
policy is bounded to one research attempt; it supplies no guard evidence.

## Required mapping

The R29 candidate needs a source-context action before inference that consumes
the exact resolved module `M`, authentic caller predecessor `P`, and unchanged
`xi`, then returns the original `(C0,w0,e0;xi)`. It must provide independent
constructors for original `j0/a0`, including exact current authority,
typed-path/observation/receipt incidence and old-dependent preservation. The
action must not evaluate expressions or effects. This section traces where
those inputs or outputs exist in the selected playground path.

## Actual caller-to-consumer path

| Stage | Current constructor/consumer | Correspondence result |
| --- | --- | --- |
| Parse and lower | `tools/inference-playground/src/lib.rs::prepare` parses the supplied source under a generated `ModuleIdentity::source_root` and calls `lower_module_with_local_source(..., SemanticImports::empty())`. `prepare_operation_v1_hir` does the same. | The selected public route has no `P`, `xi`, source-context action, `C0/w0/e0`, `j0/a0`, or original license input. |
| Source identity and declarations | `yu-hir::module::lower_module_with_counters` validates an optional caller-evidence binding against the exact module identity, parse root and admitted declaration source key. `source_annotation::declarations` constructs source IDs from family/member keys and retains visibility, signature positions, ranges and parsed signature shape. | This authenticates structural source correspondence. It does not type or authenticate an initial semantic context, current authority, event activity, typed `Path`, observation/receipt, predecessor dependency map, or original dependent witnesses. |
| Caller evidence seam | `SemanticImports::with_caller_evidence` retains `Arc<dyn Any + Send + Sync>` after checking parse-root, declaration and module correspondence. Its documentation states that this checks artifact correspondence only and does not certify payload meaning. | This can preserve a payload through exact source binding. It cannot construct or validate `P`, `init`, the old frame, `j0/a0`, or a license. Reusing it would repeat transport without the missing semantic owner. |
| Constraint generation and solve | `CandidateInference::solve_mode` walks retained HIR and local source; `ConstraintBatch::collect_candidate_mode_scoped_v1` collects constraints; `InferenceSession` solves and runs the candidate. `candidate_operation` consumes a retained source declaration/signature to build its candidate signature value. | No semantic caller-context initializer or `j0/a0` consumer appears on this path. Constraint generation/propagation does not establish the unrelated guard. Static source signature formation does not produce original `DeclContribution` or fixed-`c` permission. |
| Ordinary execution entry | `execute` calls `prepare` and completes experimental inference before `RuntimeProgram::from_hir`, then starts the source schedule. `RuntimeProgram::start` initializes `ExecutionOwner::ModuleRun`, empty active receivers and default receiving state before `begin_root(0)`. | This event is later than inference and carries no authentic predecessor, original `xi`, `theta0`, old dependent fields, or proof that it is the theorem's exact `C0,w0,e0`. It cannot supply an initial guard retroactively. It also is not the proposed pure context-forming action. |
| Separate operation-v1 research route | `execute_operation_v1_runtime_research` constructs a specialized candidate and runtime evidence link tied to one HIR, then mints a receipt only after a matching runtime completion. | That route has a concrete source/runtime correspondence for its distinct callback/handler scenario. Its later completion receipt is neither the original initial `j0/a0` nor the fixed-`c` formation license. No transfer to the current bootstrap is justified. |

## Conclusion and safe seam

On the selected path, the first possible API seam is the caller input to HIR
lowering before `CandidateInference::solve_mode`. The current caller supplies
only source text, a name and a scoped-mode boolean; `SemanticImports::empty()`
is passed. The current downstream consumer accepts constraints, not a
dependent initial context. Adding a field, opaque payload, or constructor
signature here would retain data but would not derive the original guards.

The runtime entry is not a safe substitute: it occurs after inference, begins
a dynamic source schedule, and has empty receiver activity. Treating it as
`init` would both violate the pure context-formation candidate and leave exact
same-index incidence/old-field evidence absent. Executing source before
inference would conflict with the approved inference principles, which
explicitly construct constraints without prior expression execution.

Therefore **NO_SAFE_CODE_SLICE** for a guard-producing or theorem-relevant
initializer in the inspected caller/consumer path. A later implementation
lease requires independently proved constructor inputs and a consumer that
uses the evidence without converting payload presence into truth. This audit
does not block unrelated approved inference/code work; R29 itself authorizes
no implementation. No compiler files, tests, builds, or probes were changed
or run.

## Pinned source bytes

```text
bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b  tools/inference-playground/src/lib.rs
fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46  tools/inference-playground/src/runtime/machine.rs
484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11  tools/inference-playground/src/runtime/program.rs
c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a  crates/yu-hir/src/module.rs
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f  crates/yu-hir/src/module/source_annotation.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
```

The source route was read at R29 baseline `6b427ebb7`; no code path changed
between that baseline and this audit. The earlier R28 source-owner audit
independently reported the same missing caller predecessor and source event;
this R29 audit checks the actual lowering, solving, and runtime order at the
selected route. The proof lane's pending construction/restriction result is
separate.
