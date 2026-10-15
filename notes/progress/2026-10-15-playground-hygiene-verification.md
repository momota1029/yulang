# Playground Catch and hygiene verification

Date: 2026-10-15
Status: independently reviewed bounded verification and test correction;
full hygiene, Oracle parity and soundness remain OPEN.
Starting baseline: `e9790f96f154ef0ddf67cb45aa26a569148569d7`.
Branch: `research/simple-sub-intrusion`.

## Scope and authority

The user requested detailed verification of existing Catch and hygiene behavior,
actual Yulang2 Oracle execution, and soundness. The current inference principles,
annotation integration §§1–1.1, charter §21 and compose scope-release decision
govern the expected behavior. No new language decision or compiler implementation
is introduced by this investigation.

Mode: M2 for the bounded source/proof/Oracle audit, with semantic
`compiler_referee` and Oracle/conformance `spec_auditor` review budgets; separate
M1 for the stale test contract, with one `spec_auditor` before and after writing.
Convergence requires actual executable evidence and explicit source/theorem
premises; a green test or Oracle observation cannot close soundness.

## Focused native checks

All commands ran serially with `CARGO_BUILD_JOBS=2`, `timeout 300s` and
`-- --test-threads=1`. Solver commands enabled `shadow-apply-candidate`;
HIR/core commands enabled `shadow`. Counts below use each target's final run.

| Cargo test selection | Result |
| --- | --- |
| `-p yu-hir --test catch_local_source` | 6 passed |
| `-p yu-solver --test candidate_catch_value_source` | 6 passed |
| `-p yu-solver --test candidate_operation_catch` | 12 passed |
| `-p yu-solver --test candidate_effect_annotation` | 17 passed |
| `-p yu-solver --test candidate_formal_effect_polarity` | 7 passed after the correction below |
| `-p yu-solver --lib candidate_effect::tests::` | 25 passed, 3 failed, 2 ignored |
| `-p yu-solver --lib candidate_context::tests::source_closed_annotation_filters_execute_and_keep_resolved_members -- --exact --test-threads=1` | 1 passed |
| `-p yu-core --test shadow_directional_protection --test shadow_directional_incidence_join --test shadow_typed_evidence` | 1 + 1 + 3 passed |
| `-p yu-playground --test cli catch` | 4 passed |

Final selected totals: **83 passed, 3 failed, 2 ignored**. This is not the full
workspace suite. The first two solver targets shared one Cargo invocation;
annotation and initial formal-polarity targets shared another. Eight native
Cargo test invocations ran, including the necessary post-repair formal rerun.

The three failures are the already recorded Effect fixture failures:

- `multiply_originated_bound_keeps_future_conflict_paths_through_extrusion_and_intrusion`
- `raw_and_canonical_effect_roots_replay_late_conflict_after_parent_copy_intrusion`
- `views_keep_fresh_use_ownership_and_intrusion_rollback_restores_relations`

They fail parent/copy canonical-row equality assertions in
`crates/yu-solver/src/candidate_effect.rs:2686`, `:2652` and `:3106` respectively.
Their reciprocal type-bound setup does not supply the selected source
Value-reference qualification. Establish that fixture/source correspondence at
`candidate_effect.rs` / `candidate_intrusion.rs` before choosing a repair.
Every existing assertion is preserved; these failures are not classified as
approved behavior or as source-level soundness counterexamples.

## Authorized test correction

The initial formal-polarity run had five passing tests and one failing test:
`negative_concrete_and_empty_formal_rows_still_reject_before_solving` still
expected outer `[io] int` to be unsupported. Charter §21 and annotation
integration §1.1 already require that outer computation-formal route.

Fresh pre-write `spec_auditor` review accepted removing only that outer case
from the rejection loop and preserving all four nested callback expectations.
An `implementer` changed only
`crates/yu-solver/tests/candidate_formal_effect_polarity.rs`. The renamed nested
test retains its assertions. A new no-Catch behavioral test checks:

- an argument producing `io` and `other` accepts a result allowance for both;
- an allowance for only `io` rejects the retained additional effect;
- `io` is not removed merely by the formal annotation;
- a pure argument does not acquire `io` from that annotation.

The final seven tests pass. Independent post-write conformance review found no
findings. This corrects a stale contract using existing authority; it does not
enable negative callback permission or Catch subtraction.

## Scoped source observations

Three existing examples ran once each with
`target/debug/yu-playground --scoped-experiment --intrusion`, timeout 15 seconds.
All exited zero with empty stderr. Correlation starts from the actual final
source occurrence/slot, follows its Effect relation's upper row, and checks
every recorded completed member observation at that destination, including its
Replay upper-parent identity. It does not select only one favorable route.

| Example / use | Source occurrence/slot → relation → output row | Final member observations | Protection |
| --- | --- | ---: | --- |
| identity | `25/2 → 226 → 15` | 1 | empty |
| two uses, first | `25/2 → 226 → 15` | 1 | empty |
| two uses, second | `33/2 → 382 → 22` | 1 | empty |
| independent protection | `35/2 → 317 → 22` | 1 | scope 53 retained |

The examples contain 13/23/16 total recorded member observations respectively;
all four final observations have the required state. Distinct use identities
remain distinct. These finite observations do not certify all semantic routes.
No automated scoped source-assertion test existed at the starting baseline.

The separate [16-source adversarial record](2026-10-15-playground-hygiene-adversarial-observations.md)
preserves its complete inputs and outcomes. In particular, a computation formal
accepts the admitted mixed `signal`/`write` input, but current Catch forwarding
does not establish a `write`-only residual. The callback annotation is unsupported.

## Soundness disposition and Oracle boundary

The [reviewed assurance audit](../theory/2026-10-15-playground-hygiene-soundness-audit.md)
reuses existing results for unconditional Catch effect requirements and
scope-specific release through one shared injective FreshUse map. Fresh
`compiler_referee` review found no findings in these bounded claims or the
adversarial record. Full source generation, complete activation and actual
handler permission/consumption remain explicit premises.

Current Catch forwards scrutinee and arm effects. That overapproximation neither
demonstrates protection against unauthorized capture nor proves global type
soundness. The next necessary constructor/consumer evidence is the joint
source-owned permission, operation-specific actual consumption and independent
survivor partition before enabling subtraction. The original hygiene, soundness,
principality and production gates remain OPEN.

A clean detached Oracle at `a58eefc31e22141574b6f20c6a5748151c6d79f1` was rebuilt
with the frozen lockfile, two build jobs and a 300-second timeout. The build took
70 seconds and emitted the frozen `infer` library's 105 warnings. Its source was
clean before and after building; frozen source was not modified. The executable
SHA-256 is `f44bc8e41bc70290314e166832fa2a66183390ad742de458a60d7aabd39492fe`.
The existing Oracle capture worktree contains unrelated modifications and was
not used as a frozen-source build input. The
[actual comparison](2026-10-15-playground-hygiene-oracle-comparison.md) retains
eight source families, full source constructors, command/log hashes and a
reproducible bounded [harness](../../tools/research_playground_hygiene_oracle.py).
Direct and annotated handlers return `1`; outside-arm and sibling-operation
requests remain unhandled. The mixed-effect example stops at unhandled `write`,
so its subsequent signal handling and complete residual are not observed.

Two distinctions prevent an overclaim of compatibility:

- The omitted-callback scheme retains the symbolic effect, but the concrete
  terminal program returns `1` through both the evidence VM and interpreter.
  This differs from the current selected noncapture outcome. The exact shared
  source-to-runtime cause remains unresolved; no new language decision follows.
- Frozen Oracle `answer: [] int` adds a lower constraint at its root annotation
  connector, whereas Candidate checks initializer effect against an upper.
  Identical spelling is not an equivalent purity assertion. Acceptance
  differences in these probes do not establish a compatibility defect.

Fresh `spec_auditor` review checked source adaptation, actual logs, binary
hashes, constraint direction and the extra interpreter control. No blocking or
major findings remained; the primary corrected one exact source locator.
The source map also found no alternate Yulang3 Catch runtime implementation:
current VM/native backend entrypoints are boundary stubs. Current native results
are inference observations, not successful program execution.

Verification budget: no broad workspace/legacy inference test suite and no
performance benchmarks. Timing samples and benchmark processes: zero. There
were 56 direct CLI processes: 16 adversarial native, 3 scoped native, 36 in the
comparison packet (including its help and unforced-root attempts), and 1 primary
interpreter control. This is 27 native and 29 Oracle CLI processes, separate
from the eight Cargo test commands and one Oracle build. No additional test
suite was run after record-only changes.

Native compiler source is unchanged. The test repair, research harness and
reviewed evidence were integrated; `tasks/current.md` and
`tasks/research-lab.md` are synchronized. No design authority or parent proof
status changed, and no required record synchronization is deferred. Remaining
work is the source-owned permission/consumption/survivor bridge, the three
Effect fixture qualifications, and the explicit Oracle interpretation gap.
