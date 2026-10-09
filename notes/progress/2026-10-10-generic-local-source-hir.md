# Generic local source carrier checkpoint

Date: 2026-10-10
Baseline: `334fd3599`
Scope: nonshipping HIR source formation; not local inference acceptance
Authority: current practical inference goal and Simple-sub question reassessment;
existing source-identity and braced-block syntax contracts
Mode: M2; compiler-referee and performance-auditor, followed by fresh delta review

## Implementation

`shadow::lower_module_with_local_source` forms a root-owned `LocalSource`
sidecar during HIR lowering. `HirModule::local_source` checks the owning root;
expression indices are branded with that root. Integer, resolved Name, Apply,
Group, Lambda and flat Block forms retain actual occurrences, source keys,
ranges and lexical owners. Local bindings retain their actual local identity,
ordered parameters and initializer index. Captures retain existing identities.

Sequential nonrecursive initializers see earlier bindings and outer parameters,
but not their own binder. Publication happens after initializer formation;
scope restoration preserves nearest parameter/local shadowing. This is source
formation, not solver publication. Complete roots are staged before attachment.
The source-generalize design §§2/4 supplies ownership context, not authority for
production brace inference. Ordinary lowering still rejects unsupported bodies;
the new sidecar is not yet consumed by `CandidateInference`.

## Review and repair

The initial two independent reviews identified three major findings and one
minor finding. One fresh implementer repaired the entire accepted bundle:

- Register each local parameter's actual local owner at identity creation,
  restoring the existing source-position crosswalk.
- Accept a single trailing newline, semicolon or comma, as required by the
  existing block syntax. Missing final expressions and invalid separators
  remain outside this candidate.
- Replace reverse lexical scans with a scratch spelling index and a stack of
  previous bindings; all pushes and restorations share the same owner.
- Apply the existing root parameter preallocation limit to local-source mode.

Fresh semantic and resource delta reviewers closed all accepted findings,
with no remaining blocking, major or minor correctness finding. Previously
clean planner areas were carried forward; these reviews do not certify runtime
inference, the separate solver kernel or complete Call correspondence.

## Costs and boundary

Name lookup uses expected average constant map operations plus spelling
hashing. Scope restoration is linear in popped bindings; scratch storage is
linear in active bindings and distinct active spellings. Flat block width is
not represented as a recursively owned continuation. Actual expression depth,
including synthesized parameter Lambdas, remains bounded by 128. Upstream
planning and source indexing precede that bound.

Formation includes linear arena inventories and transient completion storage;
nested recovery scans can cost O(N*D), with admitted D bounded by 128.
`retained_arena_bytes` reports arena/vector and spelling storage only: source
identity maps, shared payloads, scratch, allocator overhead and failed-attempt
peaks are excluded. Existing infallible spelling/map allocations remain; no
complete allocation-failure recovery or RSS claim is made.

## Verification

Primary checks passed without warnings on the repaired frozen dependency set:

- `RUSTC_WRAPPER= cargo check -p yu-hir --features shadow -j 2 --offline`
- `RUSTC_WRAPPER= cargo check -p yu-solver --features shadow-apply-candidate -j 2 --offline`
- `git diff --check`

The default solver check passed earlier in this slice; the repair affects only
the private shadow carrier. No tests, execution probes or measurements ran.
Measurement budget consumed: zero processes, zero samples. No dedicated callers
or runtime tests of the new entrypoint were found in the reviewed tree.

Frozen SHA-256:

- module.rs: `78e85b04785b55d28768408847b732030951e28c0789550ad18603989c119373`
- shadow.rs: `fd988f7bf1b3a5f22e9486f1069601a6837804ef4c9038ded563746de92f7718`
- module/local_source.rs: `4829031131e81c8ad36f367b9b64964a919adb988494b9c4a4d6a02d789d3a42`

## Next compiler work

Consume this source carrier with actual lexical levels and per-use freshening.
Correction from the user: solving an initializer to completion and freezing it
before continuation solving is not a general necessity; level and extrusion
handle later cross-boundary constraints. The earlier freeze-first plan is
withdrawn pending the concrete adapter audit. Distinguish the binding's level
boundary/live description from an immutable snapshot. Preserve outer captures,
top-definition dependencies and initializer evaluation effects. Existing
Simple-sub operations require no literal-only or registry-adoption question.

Current admitted solver source levels remain one. General anchor closure,
complete Call, ordinary public extraction and replacement on `yulang3` remain
open. No proof-DAG gate or full objective is declared complete.
