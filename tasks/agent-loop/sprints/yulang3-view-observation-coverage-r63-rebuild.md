# Sprint YULANG3-VIEW-OBSERVATION-COVERAGE-REBUILD-20261026/r1

Status: ACTIVE after explicit user authorization to reconstruct the missing
R63 candidate in a separate sprint.

Branch: `yulang3`.
Frozen proof baseline: `93d08d5867015741b3588ea3df4c56903b2bbe83`.
Current coordination baseline: `43473afa61a5fd7853635e134b3d40db125ec71d`.
Contract revision: r2. The primary records this contract's SHA-256 in
`tasks/agent-loop/current.json` before any worker launch.

## Original outcome and success evidence

Parent: paper execution-safety/canonical-forms scope at
`docs/yulang-operational-type-safety-ja.tex:998–1005`, with value syntax and
typing at :137–164 and :215–228, machine/value observation at :256–270 and
:299–327, plus R62's conditional `allocated_force_control` bridge.

Reconstruct a new, independently checkable represented counterexample to the
unqualified claim that closed typing supplies the R62 finite constructor-
observation premise. Preserve the exact four declarations, quantifiers,
closed witness, accepted source meaning and all R62 conditions from the prior
R63 contract. The new candidate is a new artifact; it does not inherit the
lost candidate's verification or review.

Required public declarations, under
`YulangClosure.PaperTypes.PaperObservationCoverage`:

1. `view_operand_force_typed`: arbitrary declaration table and view metadata;
   the closed force of a view-wrapped delayed unit is typed at base unit with
   empty graph/type environments.
2. `no_observation_step_from_view`: arbitrary heap, metadata, wrapped value
   and target; no `ObservationStep` starts at a top-level view.
3. `view_operand_no_literal_delay_trace`: arbitrary heap, metadata and body;
   no finite observation trace takes a view-wrapped delay to that delay.
4. `connected_executor_view_force_stuck`: arbitrary declaration table,
   binder, metadata and body; the existing connected executor returns `none`
   for the view-force state with empty stack.

Success requires exact declaration name/kind/type enumeration, complete
`#print axioms` output for every declaration, no holes or checker bypasses in
the candidate dependency cone, primary's independent verification, fresh
non-author review, and primary adjudication. Keep worker checker failure output
if any. An absent view rule is not added to make the candidate pass.

The 30 frozen source/dependency pins in the original R63 contract must match
their bytes at the frozen proof baseline. They were independently rechecked
for this sprint: 30/30 match at `93d08d5`. The coordination baseline is newer,
but the isolated proof project is reconstructed from the pinned proof baseline
and receives only the new candidate file.

## Preserved boundaries and open premises

This is a represented auxiliary-relation obstruction. It does not refute the
conditional R62 theorem, prove compiler emission of the exact term, establish
paper-machine `Bad`, prove whole-language safety, or authorize a production
semantic change. View metadata remains intact. Do not add a view transition,
erase metadata, narrow the source domain, change typing or executor rules, or
alter expected outputs.

`R62-FINITE-CONSTRUCTOR-OBSERVATION-1`, source/native correspondence, R23,
whole-language execution safety, inference A/B, and production remain OPEN.
The original R63 candidate and primary scratch outputs were lost with their
isolated `/tmp` directories. Preserve their handoffs, hashes, failed worker
audit, primary receipt, and the prior unknown reviewer lease as historical
evidence. Do not reuse the old candidate hash as evidence for this candidate.

## Proof and implementation lanes

Proof owner: one registered `lean_prover`, one assignment and no descendants.
Stages: verify all pins/tool versions; reconstruct the four exact declarations;
run one focused build and one complete audit; static-scan the full internal
import cone; freeze one handoff and stop writes. Use the pinned project
toolchain, `-j1 -M1024`, one checker owner per workspace, and no retries after
a failed call.

Implementation lane: `NO_SAFE_CODE_SLICE` within this sprint. The relevant
paper owners are `PaperHeapObservation.lean` (view is absent from the finite
observation relation) and `PaperExtendedExecution.lean` (existing executor
case split). The Rust owners are
`tools/inference-playground/src/runtime/machine.rs` and
`tools/inference-playground/src/runtime/receiving.rs`; current view/value
handling does not establish a paper view-execution rule. Changing either
relation or Rust semantics would cross
the fixed theorem scope and lacks source/native authority. No Rust files,
tests, fixtures or compiler behavior are leased.

## Exact paths and frozen seams

The old R63 directories and leases remain untouched. New workspaces:

- Proof: `/tmp/yulang-r63-rebuild-20261026/proof`
- Primary verification: `/tmp/yulang-r63-rebuild-20261026/primary`

Each workspace is a source copy of the frozen proof baseline, with the
candidate added only at
`notes/theory/lean/YulangClosure/PaperObservationCoverage.lean`. Each owner
may write only these exact relative outputs in its own workspace:

- `notes/theory/lean/YulangClosure/PaperObservationCoverage.lean`
- `notes/theory/lean/.lake/R63RebuildAudit.lean`
- `notes/theory/lean/.lake/build` (symlink to this owner's `lake-build`)
- `run_call.py`, `process-manifest.json`, `proof-checks.txt`
- `lake-build`
- `call-01.stdout`, `call-01.stderr` through `call-04.stdout`,
  `call-04.stderr`
- one shared handoff only for the proof owner:
  `tasks/agent-loop/inbox/paper-observation-coverage-r63-rebuild.md`
- one primary receipt only for Luna:
  `tasks/agent-loop/inbox/paper-observation-coverage-r63-rebuild-primary.md`
- one fresh review receipt only for the reviewer:
  `tasks/agent-loop/inbox/paper-observation-coverage-r63-rebuild-review.md`
- one primary-owned outcome receipt:
  `tasks/agent-loop/sprints/yulang3-view-observation-coverage-r63-rebuild-outcome.md`

No root import or repository source edit is authorized in this sprint. A clean
review is evidence for Luna's adjudication; any later source integration gets
its own exact paths, baseline check and verification envelope.

## Resources and stop conditions

Fresh envelope: 1,800 active seconds total: proof owner 600 seconds / four
literal checker calls / at most 150 checker seconds; primary 1,020 seconds /
four calls / at most 150 checker seconds; fresh non-author `compiler_referee`
180 seconds / zero checker calls. The four checker calls per verification
owner are resolved Lake `--version`, `lake env lean --version`, one focused
module build, and one complete audit. Each process is capped at 120 seconds.
No tests, Cargo, runtime probes, network, install/update, or full default build.
Primary verifies exact pins and artifact hashes and independently validates
all names/types/axioms in the complete captured output.

The previous R63 worker is STOPPED. Its reviewer remains UNKNOWN with the old
review lease held; do not reclaim it or reuse its receipt path. Keep the eight
legacy UNKNOWN reservations. Do not claim any Astra execution. No retry, budget
renewal, descendant, new dependency, semantic choice, or expanded write lease
is permitted. Stop on pin/tool mismatch, any candidate falsifier, a failed
checker call, unavailable required resource capacity, or exhausted budget.

Falsifiers: an actual frozen-relation observation step from view; a trace to
the literal delay; a genuine typing restriction excluding the witness; a
successful existing executor branch; or any source/hash/audit mismatch.
Fresh review covers theorem quantifiers and types, candidate and dependency
identity, complete audit, worker failure handling, represented/source scope,
and the conclusion that only the unqualified coverage premise is obstructed.
