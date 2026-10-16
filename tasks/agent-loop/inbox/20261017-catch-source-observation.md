# Frozen handoff: Catch source observation compile correction

Sprint: `catch-exit-incidence-and-source-observation-20261017`, contract
revision 2, SHA-256
`1a687d936e1d5db7ac92660ec5e6071f430e687edb6178193f1fa1a075e96fe5`.
Assignment: `assignment-catch-source-observation-20261017`, handoff revision 1.
Outcome class: provisional source/native observation instrumentation; compile
correction and static API-owner audit complete. No example execution or parent
closure is claimed.

Parent: original finite F1 source/native obligation. The proof packet's reviewed
conditional supplier obstruction `CATCH-EXIT-INPUT-1` remains open; response
entry/callback/parent and FK1, FIRST-RESULT, H1-H2, JOINT_DEC, F5,
source-Generalize/export, principality and production remain open.

Worker: `/root/catch_source_observation_impl`; current session `current-session`.
Requested model/effort: `gpt-6-luna` / high. Observed model/effort:
`UNKNOWN` / `UNKNOWN` (the exposed runtime supplied no effective-model receipt).
Luna acknowledged active work after the frozen proof STOP/CLEAN review. No
descendants or coauthors.

## Exact change and owner audit

The frozen example had two E0308 calls passing owned `LocalSourceIndex` values
to `LocalSource::expression(&LocalSourceIndex)`. Both calls now borrow the
arm-body index:

```diff
- result_source.expression(operation_arm.body)
+ result_source.expression(&operation_arm.body)
- result_source.expression(value_arm.body)
+ result_source.expression(&value_arm.body)
```

No other example content changed. The source audit checked the exact pinned
owners: `LocalSourceIndex` is a distinct owned index and `LocalSource::expression`
accepts a reference and checks owner identity before lookup
(`crates/yu-hir/src/module/local_source.rs`); the HIR root, source, declaration,
and occurrence lookup methods authenticate ownership
(`crates/yu-hir/src/module.rs`); ordinary `CandidateInference::solve` enters
source preflight, candidate constraint collection, and the inference session,
while `observes_hir`, `candidate_conflicts`, and `export` retain their artifact,
conflict, and authentic-root checks (`crates/yu-solver/src/shadow_apply.rs`).
The borrowed `source_call` is indexed over retained source Calls, and
`fresh_use` is optional and conflict/occurrence gated (same owner). No API call
in the example relies on `solve_scoped_experiment`, a direct internal constructor,
or a Simple-sub bypass. All other `LocalSource::expression` calls pass borrowed
indices.

The literal remains exactly the 138-byte test specimen, SHA-256
`9a86d2e0d0004cbdbd4be96dcdc284b6648287a203518c93211c43705f8ed8d3`, and a
static comparison against
`crates/yu-solver/tests/candidate_operation_catch.rs` matched it byte-for-byte.
Existing declaration/root/source-key/occurrence/binder/use checks, authentic
source-call association, ordinary solve, conflict fence before fresh-use or
exports, and actual HIR roots remain intact.

## Source/native correspondence and limits

The instrumented path is the existing HIR `LocalSource` Catch construction
(`local_source.rs`, including arm body indices and occurrence/source identities)
-> ordinary candidate source preflight and constraint collection
(`crates/yu-solver/src/candidate_source.rs`) -> solver propagation through
`InferenceSession::run_candidate` (`shadow_apply.rs`) -> gated borrowed
`source_call`, optional `fresh_use`, and authentic-root graph exports. This
handoff establishes only the static call/API correspondence. The example is
not yet run, so parse/HIR/candidate observations are unknown; even a successful
candidate run would not establish complete Catch typing, handler adequacy,
detached export, runtime behavior, the missing typed handler-exit-to-matcher
incidence, or F1 closure. Source observation remains provisional. Luna owns
cleanup if falsified or no longer useful; the explicit falsifier is any mismatch
in the pinned literal, HIR/source identities, actual API ownership, conflict
gate, or source-call occurrence correspondence.

Reused prior evidence: the rev2 proof/handoff reviewed as a conditional supplier
obstruction; the prior Catch source/export handoff and repair receipts for the
authentic scrutinee spine, identity checks, conflict fence and API design; and
the pinned source/candidate owners. Rejected as evidence: prior fixture output as
a fresh run, prior scalar candidate assertions as source typing, a borrowed
graph as detached export, and every withdrawn Simple-sub bypass. No diagnostics,
test expectations, source domain, inference semantics, or proof claim changed.

## Freeze, checks and resources

Baseline example and Luna-owned pre-write snapshot both matched SHA-256
`325a6807cd2423bc941083264118138f51055cdf426506bb2a9e380f0b5b361e`.
All 61 rev2 dependency pins matched at entry. At freeze, all 60 immutable
dependencies matched; the one expected mismatch is the leased example, now at
the output hash below.
Static checks: exact two-line diff; all `LocalSource::expression` arguments
borrowed; test literal byte equality and length/hash; API-owner call-site audit;
contract and dependency hash validation. No test, build, Cargo, executable
example, Git, manifest, library, or test edit was performed.

The frozen example SHA-256 is `243bb0d1e328ed951576ff37eda70007e708cc461a81e9999e69bd38dae41abb`.
The exact new paths/leases are:

- `crates/yu-solver/examples/research_catch_source_export.rs`
- `tasks/agent-loop/inbox/20261017-catch-source-observation.md` (this file)

No scratch or generated paths were created. Active work charged: 63 seconds of
360; 297 seconds remain. CPU and peak memory were not measured. One initial
Cargo invocation remains available only after fresh independent pre-run CLEAN
review and Luna acknowledgement. The optional single mechanical compile-only
repair remains capped at 80 seconds, requires its own frozen delta and CLEAN
review, and permits a second/final Cargo invocation only if invocation 1 fails
before any example execution. Any actual example execution ends run authority.

State: STOPPED after freezing this handoff and the example; no pending process
or descendant. Frozen review target is the above example bytes plus the
unchanged rev2 dependencies. Luna owns independent review and any subsequent
invocation decision. Stage-ready request, if independently CLEAN and approved:
`cargo run -p yu-solver --example research_catch_source_export` with a 120-second
timeout, as the sole authorized first invocation.
