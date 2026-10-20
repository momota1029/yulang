# R145 source trace: first unpinned syntax-admission premise

Status: **candidate source evidence; contract result 2; stopped at dependency boundary**.
Author: `/root/r145_proof`, no contributing descendants. This author does not
independently certify the result. Parent R70/R71, higher Simple-sub A/B,
source/native correspondence and production gates remain OPEN.

## Fixed parent and actual result

The parent is `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`, specifically its
`R70-ENTRY-WF-1` source-construction bridge and the retained
`R144-RAW-CANONICAL-SUPPLIER-1` consumer-adequacy question. Its original
production-reachable source domain and universal quantification are unchanged.
R145 rev1 asks for one finite authentic history from the exact input through
merge, a later raw `Work::Bound` slot, all relevant raw preimages and a real
relation-specific consumer, or the first missing premise.

The first missing premise occurs **before HIR admission or candidate solving**:
the frozen manifest does not contain the implementations of
`yu_syntax::scan_header`, `yu_syntax::parse_file`,
`SyntaxEnvironment::empty`, or `ParsedFile::syntax_diagnostics`. The pinned
playground caller shows that those operations control the admission branch; it
does not establish their result on these bytes. No unpinned syntax
implementation, HIR lowering implementation or test-helper implementation was
read. Luna confirmed this stop boundary during the assignment.

This is a dependency-boundary result, not a proof that the input is rejected,
a source-qualified falsifier, or a compiler defect. No accepted-source history
reaching the merge or later raw consumer is established here.

## Pinned prefix and precise cut

The input `tools/inference-playground/examples/nested-recursion.yu` is exactly
47 UTF-8 bytes, including its terminal newline:

```text
my loop x = { my helper y = loop y; helper x }
```

For a successful file read with this path and `--intrusion` (without `--run`
or `--scoped-experiment`), the pinned dispatch is:

| Stage | Pinned owner | What the bytes establish |
| --- | --- | --- |
| Read source | `tools/inference-playground/src/main.rs:68–78`; `src/lib.rs:40–51` | File contents pass the 65,536-byte cap and UTF-8 check, assuming the file read succeeds. The inference arm calls `infer_with_scoped_experiment(source,name,true,false)`. |
| Enter preparation | `src/lib.rs:97–98`, `266–277` | `prepare` precedes observations; the source-length check succeeds for 47 bytes. |
| Syntax admission boundary | `src/lib.rs:278–286` | Caller invokes `scan_header`, `SyntaxEnvironment::empty`, `parse_file`, then the fallible syntax-diagnostics query. Their implementations are absent from the frozen manifest. Whether diagnostics are successfully available and empty is the first unsupported transition. |
| Downstream guarded calls | `src/lib.rs:294–307` | Nonempty diagnostics return before lowering. Only after the empty-diagnostics branch does the caller invoke `lower_module_with_local_source`, then the ordinary `CandidateInference::solve` arm because `scoped=false`. These are locators, not reached events in a proved history. |

The required next evidence is the actual syntax-owner derivation that these
exact bytes produce a parsed module with a successful empty-diagnostics query,
under the empty syntax environment and header scanner used by this caller.
No runtime probe or test run substitutes for the missing pinned construction
under this revision. SourceText/standard-library allocation and successful I/O
are ordinary availability assumptions here; they do not imply syntax admission.

## Why the merge locator does not cross the cut

Pinned `crates/yu-solver/src/shadow_apply.rs:2381–2403`,
`candidate_graph_row_hashing_uses_merged_representatives`, passes the same
program text without its terminal newline to
`crate::candidate_lifecycle_retirement::hir`, calls `CandidateInference::solve`,
and asserts that some retained parent/copy has distinct raw identities, equal
representatives and a same-SCC source event. This is a checked-in expectation
and useful merge locator. Its HIR helper is outside the manifest, it was not
read, and the test was not executed. Neither a test expectation nor source-text
similarity proves this caller's syntax/HIR admission or accepted-source
reachability. No concrete parent/copy ordinal is selected by this packet.

The pinned `crates/yu-hir/src/module/local_source.rs` contains source-carrier
formation code but does not supply the missing syntax admission implementations.
Its test callsites of `lower_module_with_local_source` likewise do not establish
the earlier empty-diagnostics branch. I did not substitute a manually assumed
HIR, direct solver-helper call, fixture, or schedule for that branch.

Accordingly no physical raw slot or canonical key is selected; no raw-preimage
census, fiber cursor, witness/dependency/transform sequence, relation-local
`post_check_context`, residual/provider/attachment supplier, or scoped payload
is asserted. `Work::Bound` remains the requested later physical-slot route;
`IncomingAllowance` is a separate route and supplies no admission evidence.
An absence of those records in this incomplete trace says nothing about their
presence in a real accepted execution.

## Application, reuse and exact follow-up

Application to R70: the finite proof prefix is cut before the production-entry
predicate can be established for this example. It therefore cannot instantiate
R70's conditional extrusion theorem, discharge R71's raw/canonical supplier
premise, or refute either parent. The reduction is an exact dependency/input
requirement for the chosen source-directed method, not a new conditional
version of the raw/canonical theorem.

Reused within premises: R70 fixes its entry-to-return invariant and universal
entry bridge; R71 distinguishes forward canonical attachment from raw-key
coverage; R144 identifies the later consumer-adequacy seam and why endpoint,
fiber-ID or payload equality cannot supply relation-specific evidence. Their
historical authors and review statuses remain those in the frozen originals.
Rejected here: treating the merge regression as observed admission; assuming
parser acceptance from recognizable syntax; importing an assumed graph or
manual schedule; calling missing pinned evidence a compiler failure.

Mutual TODO `R145-SYNTAX-ADMISSION-PINS-1`, owner Luna/source-admission lane:
under a sequential reviewed contract revision, identify and pin the defining
source owners and necessary transitive constructors for `scan_header`,
`SyntaxEnvironment::empty`, `parse_file`, and
`ParsedFile::syntax_diagnostics`. Required input is this same 47-byte file,
the same caller and empty environment; required output is the first actual
admission derivation or exact rejection. Falsifier for that local success
claim: the actual owners produce nonempty/unavailable diagnostics for these
bytes. No new input, source restriction, observer or production edit is requested.
If syntax admission succeeds, inspect the actual
`yu_hir::shadow::lower_module_with_local_source` owner before assuming the
candidate-HIR entrance; its implementation is not supplied merely by the
pinned caller or local carrier file. No further in-envelope trace step is
authorized after this stop condition.

## Frozen inputs, checks and resource receipt

Contract rev1:
`tasks/agent-loop/sprints/source-lineage-trace-20261020-r145-rev1.md`, SHA-256
`728e5884f1750eac69d4d2c3359084afceea313012391fc2f320e3990aef952e`.
Baseline: `619d275c75a465ffefd3875a92640387d1599804`; explicit activation
receipt supplied by Luna: `caef8f4b8`; last primary-supplied live pin receipt:
`b9f1942ed4f395b7989eacb137baf14993325231`. The leaf independently compared
all 38 live dependency SHA-256 values to the contract manifest and found 38/38
matches at 2026-10-20 01:45:11 UTC. Baseline-object equality is Luna's supplied
receipt; the leaf performed no Git operation. The exact 38 direct hashes are
incorporated by the immutable contract hash above, rather than re-listed.

Checks: bounded static reads/searches, live input/dependency hashing, exact
leased-output path checks. No tests, builds, compiler/runtime probes,
instrumentation, new fixtures, external contact, Git, semantic/code changes,
shared-state writes, scratch files or descendants. Only this theory and the
exact assigned inbox are new paths. Requested routing: Sol/high; observed
model/effort: UNKNOWN. The hard proof grant is 900 active seconds. Exact
launch-to-stop elapsed and CPU/RSS were not instrumented and remain UNKNOWN;
conservatively retain the full 900-second reservation, with no refund or
extension claimed. The final inbox records the write-cessation timestamp and
artifact hash. This is pending fresh independent review and Luna intake.
