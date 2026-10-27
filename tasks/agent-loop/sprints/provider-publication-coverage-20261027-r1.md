# PROVIDER-PUBLICATION-COVERAGE-20261027/r1

Status: Luna-admitted successor to `PROVIDER-SOURCE-SOLUTION-REALIZATION-20261027/r1`.
Parent: unchanged full Yulang inference/executor correctness; all parent gates OPEN.
Baseline: `b54ae2df5dd0113779ee95d380cfcbdbd2fb14e0`, branch `yulang3`.
Prior sprint outcome: `tasks/agent-loop/sprints/provider-source-solution-realization-20261027-r1-outcome.md`.

## Fixed outcome

Resolve the publication-coverage obstruction for the unchanged provider fixture
`pub id x = x\n` without changing source semantics or narrowing the supported
language. Establish either (a) a source-qualified proof that the universal
open-execution judgment cannot be realized by finite-support publication maps
under the stated admission assumptions, or (b) an admissible map construction
that covers every original admitted Return while preserving prior records and
the complete provider judgment. In parallel, execute the unchanged Rust source
fixture through authentic HIR/source owners and identify the first owner of
Context, Return admission, replay and publication coverage. The source lane may
show that an assumption is inapplicable only with actual owner evidence.

This packet does not claim a provider counterexample merely from the abstract
fresh-occurrence obstruction. It does not authorize compiler semantic changes,
production certificates, or parent-gate closure. Complete import-root
elaboration remains a separate obligation.

## Authority and direct pins

The fixed parent is `notes/theory/2026-10-13-intrusion-source-preservation-proof.md:16–44`,
with correction `notes/theory/2026-10-24-birth-level-scc-intrusion.md:2–6` and
Authoritative algorithm `notes/design/2026-10-11-yulang-inference-top-level-principles.md`.
The prior r1 contract and amendment govern unchanged source semantics and
remain pinned above. Direct source/proof inputs at admission:

| Path | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `notes/theory/lean/YulangClosure/OriginalProviderSourceSolution.lean` | `3bf66649fdf4baacb3140de7786165db0d2b138087ca582bd32008b87a95a21a` |
| `tasks/agent-loop/inbox/provider-source-solution-20261027-review.md` | `9ac6965b0ead4afd486b3526bc1148d0005edcdcf6711f9a70c8e0fdcd38f1be` |
| `tools/inline-authentic-extraction/src/bin/original_provider_reify.rs` | `5ed03633e8a37775847d7c28fc08d2d7acc98965299e0dbe27568b266fd2b8ed` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-hir/src/module/source_exports.rs` | `03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179` |

All additional direct inputs must be hashed in the owning handoff before use.
The failed r1 adapter and audit remain immutable evidence; do not overwrite the
frozen proof module, r1 handoffs or review.

## Leases and required work

**Constructive proof — registered `lean_prover`:**

- Write only `notes/theory/lean/YulangClosure/OriginalProviderPublicationCoverage.lean`,
  `notes/theory/lean/AuditOriginalProviderPublicationCoverage.lean`, and
  `tasks/agent-loop/inbox/provider-publication-coverage-20261027-proof.md`.
- Scratch only under `/tmp/yulang-provider-publication-coverage-20261027/proof/`.
- Formalize the actual universal `executionOpen` and `Admitted` definitions.
  Prove or refute nonexistence of a judgment with any finite-support map under
  open replay, one genuinely admitted Return payload, empty prior publications,
  and arbitrary occurrence re-scoping. Do not merely show one finite list misses
  a key, and do not infer these assumptions for the authenticated provider.
- Separately investigate a total-function extension over all admitted Returns.
  State exact compatibility and source-rule premises needed to preserve all
  prior records and the complete judgment. A construction conditional on an
  assumed provider judgment is not closure; apply the result to `PSR-EVENT-MAP-1`.
- Use the pinned Lean 4.35.0 project. At most 8 Lean/Lake/checker calls and 600
  seconds total, 1 CPU / 1 GiB / 180 seconds per process; one verification owner.
  Final call is reserved for every delivered theorem type and complete axiom
  audit. No `sorry`, project axiom, changed admission, successful Kernel
  assumption, or external package.

**Rust source owner — registered `implementer` (Luna/high):**

- Exact write leases: `tools/inline-authentic-extraction/src/bin/original_provider_reify.rs`,
  `notes/theory/lean/YulangClosure/OriginalProviderPublicationCoverageTrace.lean`,
  and `tasks/agent-loop/inbox/provider-publication-coverage-20261027-source.md`.
- Scratch only under `/tmp/yulang-provider-publication-coverage-20261027/source/`.
- Start from the frozen r1 adapter hash above and its complete two compiler
  logs. Repair only adapter-owned Rust errors; use the unchanged fixture bytes
  and actual HIR/CST/source-export owners. Execute foreign-parse and foreign-HIR
  rejection checks before emitting provenance. Join both explicit `identity`
  and implicit prelude `id` to the exact provider export.
- Trace only constructor-owned data. Do not fabricate original Source
  coordinates, Context, Return/Shared values, replay, finite coverage, or map
  equations. If a cross-system owner is absent, report the first exact owner gap.
  Trace is provenance only and is not an adopted schema or semantic certificate.
- At most two `cargo run --offline --locked` processes, one at a time, isolated
  `CARGO_TARGET_DIR`, 1 CPU / 1 GiB / 180 seconds each. No tests, production
  crate changes, manifests, locks, dependencies, formatters or Git.

**Fresh independent review:** after both handoffs freeze, a non-author
`compiler_referee` reviews the two new artifacts and their source correspondence.
Read/hash only; no Lean/Lake/Cargo/tests/formatters/Git. Luna owns
`tasks/agent-loop/inbox/provider-publication-coverage-20261027-review.md`.

## Envelope, falsifiers and stop conditions

Fresh sprint ceiling: 3600 seconds total (proof 1500, source 900, review 600,
Luna 500, dispatcher 100); Astra 0; at most 6 active/reserved/unknown
assignments; one verifier; tests 0. Prior sprint consumption remains recorded
and is not reset. Keep UNKNOWN legacy worker observations and quarantined paths.

The negative theorem fails if re-scoped occurrences are not all admitted or
their publication keys collide. The total-map route fails on a conflicting
complete record or any uncovered publication premise. Authenticated source
evidence can show an assumption inapplicable but cannot itself establish
Judgment preservation. Any semantic conflict, dependency drift, overlapping
lease, resource limit or genuine source-qualified counterexample returns to
Luna for adjudication. Freeze artifacts and obtain fresh independent review;
all broader inference, soundness, principality, termination and effect-hygiene
gates remain OPEN.
