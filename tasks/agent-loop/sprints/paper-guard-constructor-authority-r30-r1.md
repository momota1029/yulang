# Sprint PAPER-GUARD-CONSTRUCTOR-AUTHORITY-20261026/r30 — resolve the paper guard boundary

Status: CANDIDATE until Luna freezes this contract and grants the exact leases.
Branch: `research/simple-sub-intrusion`
Baseline: `f7a8ade138d1abec51a204b36fe5e4b06f856ce9`
Contract revision: r1.

## Original outcome and success evidence

Original parent: the immutable graph-extension and recursive-value obligations
in `docs/yulang-operational-type-safety-ja.tex:180–196,258–267,980–1010`.
The full paper claim requires every recursive cycle to pass a genuine guarding
constructor, preserves old graph nodes/types, and yields finite typed
observations. R29 is accepted only for finite block payload allocation; it
leaves the graph guard, source-formal correspondence and full paper theorem OPEN.

This source/authority packet maps every `PaperExecutionSyntax.Value`
constructor to the evidence that decides whether graph-guard traversal may stop,
must follow specified children, or remains unresolved. It must distinguish the
paper's explicit cycle criterion from later operational elimination steps and
from accepted research-grammar projections. For every row, record: constructor,
recursive child positions, candidate barrier/traversal/undetermined status,
exact source locator and wording, retained typing/evidence needed for finite
observation, and whether that source actually grants a proof-relevant
classification. A supported classification is a source fact only when the
paper or a reviewed, in-scope correction explicitly determines it.

Success is either (a) a citation-complete classification for the full represented
`Value` grammar with no borrowed research-only assumption, or (b) the first
unresolved constructor, the missing rule/definition, its exact owner/authority
path and the next discriminating evidence. An exact blocker is a useful outcome;
it does not authorize inventing semantics, a Lean guard projection, or changing
the paper. In either case preserve all original quantifiers and keep the parent
guard theorem OPEN unless its own premises are established.

The audit must include variable/reference, literal, tuple, sequence, record,
variant, nominal, both lambda modes, delay, wrap and both adapters, type
abstraction/application, both union injections, intersection (`both`), roll,
top, view metadata, and raw continuation. It must separately examine graph
references inside data payloads, lambda/delay/wrap/continuation code, and adapter
code; do not infer a child-edge rule from a type alone.

## Exact authority and frozen dependencies

- Operational manuscript: `docs/yulang-operational-type-safety-ja.tex`,
  SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
  It labels itself an unreviewed research manuscript; it is the specified
  mathematical target, not production semantic approval.
- Source manuscript:
  `docs/yulang-source-type-safety-ja.tex`, SHA-256
  `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`.
  Its SCC/closure clauses are evidence only for their stated source grammar;
  do not silently identify them with the operational heap.
- `PaperExecutionSyntax.lean`: `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- R29 `PaperFreshHeapAllocation.lean`:
  `7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925`.
- Accepted finite-guard research model `GuardedValueGraph.lean`:
  `4d2c3b17d0ab8d12606c875638426167ce596492167cecf042eb222436229f55`.
- Accepted finite cycle/rank result `FiniteGuardDecision.lean`:
  `a9924ab2c8d96a173c886ddfbb2580a7719fbf08064d9f85d0644784778de9fa`.
- Accepted higher-order allocation/guard result `HigherOrderRecAllocation.lean`:
  `30a6e1855fb8bb4950ad2bdfad238e000554563cb0d1d4b1ec311e3c0cf4f0dd`.
- Accepted higher-order observation `HigherOrderGraphObservation.lean`:
  `8817db7bc5181481745f49696d7b7d2e4dc927a715353ab83bc36f4ed53420cc`.
- Accepted higher-order safety `HigherOrderGraphSafety.lean`:
  `de67122c098579b5ba088ff832ef8ca36e233537faf064ab8e36520cf2532533`.
- Prior accepted guard outcome:
  `tasks/agent-loop/sprints/guard-interaction-theory-20261025-r1-outcome.md`,
  SHA-256 `9bffe30363b2830eb8fafcb5af837541cb7ba3314e9daa73013e4865f56fd4e5`.
- Prior R29 adjudication:
  `tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-adjudication.md`,
  SHA-256 `d6523cba7a7b68871f56d359168f37d83bef27fa8ae2081777094e794b3cbea7`.

The finite rank decision is already accepted for its `GuardedValueGraph`
`Node.next` domain. HigherOrderRecAllocation/GraphObservation/Safety are
accepted for their distinct HigherOrder grammar and exact projections. Reuse
those facts only as comparisons or within their exact domains; do not copy their
barrier projection into `PaperExecutionSyntax.Value` without a source bridge.
The recorded B-PAPER-1/GVG-FORMS-1 and B-OBSERVE-1 boundaries remain OPEN.

## Two continuing lanes

**Primary source/proof intake, Luna:** independently read the frozen manuscript,
source manuscript, paper syntax, R29 handoff, accepted HigherOrder guard and
observation results, and the cited operational call/view/type rules. Produce
the final row-by-row source/authority table and adjudicate the first unresolved
constructor. Record a concrete falsifier for every claimed barrier and every
transparent edge. Do not run Lean/Lake, Rust, tests, runtime probes or modify
syntax/semantics.

**Complementary research lane, one registered `researcher`:** compare the exact
paper and source clauses against `PaperExecutionSyntax.Value` and the accepted
HigherOrder projection. Write only the assigned research handoff, with exact
quotes kept short, line/section locators, byte hashes, candidate row statuses,
counterexamples to unsupported classifications and a precise missing owner if
the source is silent. Do not decide authority, modify source/semantics, run any
checker/test/runtime command, read or write another lane's outputs, or start
descendants. Requested and observed runtime identity/model/effort are recorded
separately; UNKNOWN stays UNKNOWN.

**Implementation lane:** `NO_SAFE_CODE_SLICE`. This sprint changes no Rust,
source behavior, tests, diagnostics, snapshots, expectations, configuration,
or public documentation. The existing R29 inspection of
`runtime/program.rs` and `runtime/machine.rs` remains the nearest native owner
evidence; without a paper-constructor classification and source/native graph
relation, an implementation change would be unsupported.

## Permissions, leases, review and resources

Primary owns this contract, `tasks/agent-loop/current.json`, and the primary
result `tasks/agent-loop/inbox/paper-guard-constructor-authority-r30.md`.
Researcher owns only
`tasks/agent-loop/inbox/paper-guard-constructor-authority-r30-research.md`.
After both source writers STOP, one fresh non-author M1 `spec_auditor` may write
only `tasks/agent-loop/inbox/paper-guard-constructor-authority-r30-review.md`.
Reviewer may verify quotations, citations, complete constructor inventory,
research-domain boundary and exact status labels; no Lean/cache access or
checker call. If the role's read-only instruction prevents a file write, return
the report to Luna to persist without changing its content.

The aggregate sprint cap is 600 active seconds: primary <=240s, researcher
<=180s, reviewer <=180s, including descendants (none authorized). Lean/Lake,
Rust, build/test, runtime and benchmark calls: **0**. Source reads and hashes are
allowed; each process is at most 1 CPU, 1 GiB, 120 seconds. No code or source
semantic edits. No Astra assignment; available active capacity is limited by the
8 quarantined UNKNOWN reservations and shared global ceiling. No budget transfers
from R29 or previous sprints.

Stop if exact source bytes/authority change, the requested role or receipt is
unavailable, a writer reaches its cap, an authority decision is required, or a
claim cannot be grounded in the frozen inputs. On STOP, freeze the exact handoff
and record actual runtime, model/effort observations, hashes, cessation and
remaining premise. A clean review may only support a sourced classification or
the exact blocker; only Luna adjudicates and synchronizes current state/Git.

After adjudication, consult `next_action_selector` at this sprint boundary.
Keep the original full guard theorem and all source/native, inference/executor,
A/B and production parents OPEN until their own complete premises are proved.
