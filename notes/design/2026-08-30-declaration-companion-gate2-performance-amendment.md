# Declaration companion Gate 2 semantic-work performance amendment

Status: Authoritative

Scope: declaration-companion Gate 2 ordinary-path performance and verification contract after the
static-specialization and duplicated-loop whole-process rollbacks.

Approved-by: user

Approved-at: 2026-08-30

User-direction: the user selected the semantic-work gate, explicitly directed that testing and
measurement remain bounded, and approved the independently reviewed exact clauses on 2026-08-30.

Drafted-by: `architect`

Reviewed-by: independent `performance_auditor` and `spec_auditor`

Supersedes, once Authoritative, only the following exact clauses:

- in `2026-08-30-declaration-companion-with-addendum.md` §9, the final rollback sentence's conjunct
  “or measurable time/RSS regression outside repeated-run noise”; every preceding item-level dynamic
  work, rescan, allocation, range, and recovery rollback condition remains;
- in that document's §13 Gate 2 entry, only the sentence “Run performance inspection and baseline
  measurements before continuing,” replacing it with §§5–7 below;
- in that document's §14, only the paragraph beginning “Performance evidence for Gate 2 uses fixed
  1k and 10k” and ending “rolls the extraction back”;
- in that document's §13 review paragraph, only the Gate 2 reviewer set, replacing four fresh
  implementation reviewers with the M2 delta-review rule in §9 below;
- in `2026-08-30-declaration-companion-gate2-recovery-amendment.md` §4, only the final bullet
  “ordinary wall time or peak RSS outside the approved zero-effect repeated-run protocol”;
- in that amendment's §5 final bullet, only the phrases requiring four fresh independent reviewers
  and the fixed 1k/10k ordinary, companion-heavy, and malformed-comment stress measurements. The
  focused and package tests in that bullet remain mandatory under §7 below.

It does not supersede grammar, CST/AST, recovery ownership, comment-scanner order, state restoration,
gate ordering, or Gate 3's lack of authorization.

## 1. Problem and decision

Both Gate 2 shapes allowed by the original §9 reached semantic and conformance closure while remaining
production-unreachable, yet failed the whole-process zero-effect test. The static specialization
crossed the peak-RSS threshold on two 10k indented cases. The duplicated companion-only thin loops
crossed both wall and RSS thresholds on every ordinary case even though the accepted ordinary loop
bodies did not acquire companion work. Those measurements do not establish that binary layout caused
the changes, but they show that whole-process wall/RSS zero effect is not a reliable discriminator for
the intended invariant.

Gate 2 therefore protects ordinary parsing by executed semantic work rather than by requiring an
unchanged whole executable image. It introduces no tolerated slowdown or RSS allowance. A bounded
timing sample remains a diagnostic that may expose a missing proof, but whole-process time/RSS alone
does not pass or roll back the gate.

## 2. Owning responsibilities

- Ordinary valid Statement-sequence control flow remains owned by
  `crates/yu-syntax/src/grammar/expression.rs`.
- Canonical malformed-run recognition remains owned by one sink-free helper in `grammar/expression.rs`.
- Declaration-companion sequence shells remain owned by
  `crates/yu-syntax/src/grammar/declaration/companion.rs`.
- Gate 2 remains production-unreachable.

The ordinary accepted hot path is a valid ordinary AST/direct Statement sequence with accepted
separators and a valid close or dedent. Malformed-item and missing-separator recovery are outside that
accepted path and retain their own explicit contract.

On the ordinary accepted hot path, Gate 2 may add no:

- semantic condition or runtime companion mode;
- probe, candidate query, recognizer pass, traversal, rescan, or call;
- allocation, clone, cache, side vector, replay, or global initialization;
- dynamic dispatch, closure/function-pointer dispatch, or companion/Derives query.

Existing semantic operations and their per-item call counts remain unchanged. Whole-binary text
layout, symbol order, addresses, and process peak-RSS placement effects are recorded separately and
are not themselves ordinary-path work.

## 3. Gate 2 implementation topology

Gate 2 uses the duplicated companion-only thin-loop shape. It does not attempt another ordinary-loop
extraction, a third general sequence abstraction, or crate/feature isolation.

The following ordinary accepted-path bodies remain unchanged:

- `parse_statement_sequence`;
- `parse_braced_statement_sequence`;
- `commit_statement_sequence`;
- `commit_braced_statement_sequence`;
- `commit_statement_sequence_statement`;
- `commit_canonical_statement`.

Gate 2 adds exactly four production-unreachable companion adapters: AST indented, AST braced,
direct-CST indented, and direct-CST braced. Normal companion Statements call
`parse_canonical_statement` or `commit_canonical_statement` directly. The companion shells reuse
narrow sink-free separator and boundary decisions without a general sequence mode. Candidate
recognition remains limited to malformed retry and missing-separator synchronization. Companion AST
owns its one result vector; direct CST streams once.

Only the recovery-amendment-authorized ordinary helper bodies may change:

- `direct_canonical_statement_candidate`;
- `braced_next_statement_leading`;
- `statement_sequence_error_retry`.

The first static-specialization shape remains rejected because it restructures ordinary loops.
Separate crate or feature isolation remains rejected because it adds architecture and build-surface
complexity solely to influence binary placement.

## 4. Recovery amendment

The Authoritative comment-atomic canonical Statement recovery correction remains required. Its
ordinary call edge begins only after direct canonical Statement commit has failed, so it adds no work
to the defined valid ordinary hot path. Scanner order and comment atomicity remain exactly those in
`2026-08-30-declaration-companion-gate2-recovery-amendment.md` §2. Valid ordinary behavior and every
non-comment recovery contract remain protected.

The one shared declaration-intro predicate required by the recovery amendment §3 remains mandatory
for direct and input-only canonical Statement candidate queries. A complete call-site audit must show
that the shared predicate adds no accepted-path query or duplicate recognizer work.

## 5. Static proof before timing

Before any timing run, Gate 2 records the pre-edit baseline tree ID and candidate tree ID. The proof
artifact includes a reviewed source diff for the six protected ordinary bodies and every call site
of the three permitted recovery helpers.

The operation ledger has separate AST-indented, AST-braced, direct-indented, and direct-braced rows.
Each row covers the first accepted item, a separator-followed accepted item, and the valid terminal
dedent or close. Every row names the executed direct calls, probes/recognizers, semantic branches,
traversals, allocations/clones, and before/after per-item count. Any unmatched edge or changed count
fails the zero-work proof.

The proof also records:

1. no production edge from ordinary entrypoints to companion adapters;
2. no new static initializer, cache, table, trait object, closure, replay, indirect dispatch, or
   ordinary-path allocation;
3. every call site of the shared declaration-intro predicate and the three permitted recovery
   helpers.

Executable text/data/BSS size changes are recorded as binary-layout evidence, not as a threshold.
Machine-code byte identity is not required because relocation, symbol placement, and code layout are
outside the semantic-work gate. Source/control-flow equivalence and executed call-count/allocation
evidence are required.

## 6. Bounded diagnostic measurement

Measurement asks only whether a timing anomaly reveals ordinary executed work missed by the static
proof. It is not publication-grade certification.

- Build baseline and candidate with the same toolchain, profile, features, and rustflags. Exclude
  compilation from samples.
- Use one representative ordinary case: `indented_direct`, 10k items, with ×8 internal repeats. This
  had the largest estimated wall effect in the duplicated-loop rollback and avoids adding a second
  dimension.
- The ignored harness constructs source and operator table outside the timed repeat, enters the
  already-positioned ordinary sequence core rather than a root parser, retains/black-boxes the final
  result, and performs item-count, consumed-range, recovery-count, and losslessness validation once
  outside the repeated kernel. Baseline and candidate use byte-identical harness source; the durable
  evidence records its source identity and exact extraction or comparison command.
- Pin samples to one CPU and preflight for Cargo, rustc, and test contention.
- Run one warm-up pair and three measured pairs, alternating order: two warm-up processes plus six
  measured processes, exactly eight benchmark process invocations total.
- Enforce a hard ten-minute stop for the entire measurement phase.
- Record every wall/RSS pair, median, and range. Do not bootstrap, multiply layouts/modes/scales, or
  time companion/comment-stress cases in Gate 2.
- If a sample is invalidated, report the measurement incomplete. Do not extend beyond eight process
  invocations or ten minutes.
- A wall/RSS difference alone neither passes nor rolls back Gate 2. It creates no tolerated
  percentage. An anomaly triggers one delta audit within the existing reviewer budget; rollback
  occurs only if that audit finds added executed ordinary work or cannot close the static proof.

One representative production companion measurement is deferred to Gate 10 under a fresh ordinary
budget. Any plan above eight process invocations or ten minutes follows `rules/performance.md` and
requires approval before execution; no design clause itself grants an extension.

The durable evidence report records the semantic work unit, exact baseline/candidate revisions,
harness path and command, repeat semantics, toolchain/profile/features/rustflags, CPU and contention
preflight, sample order and every result, process/time budget consumed, median/range, conclusion, and
remaining uncertainty.

## 7. Functional verification budget

Gate 2 uses:

- one table-driven ordinary recovery group covering line, nested/unterminated block comments,
  internal identifiers/separators/all fixed closes, `/` prefix/nullfix behavior, and non-comment
  sentinels;
- one table-driven companion sequence group covering AST/direct × indented/braced,
  valid/retry/retained-boundary behavior, losslessness, and seeded state restoration;
- static proof that valid companion items never invoke the recovery candidate helper;
- focused Gate 2 checks during implementation;
- `cargo test -p yu-syntax` once on the closed final Gate 2 candidate.

Every other recovery-amendment §5 requirement remains mandatory: exact ordinary non-comment
before/after families; line, nested/unterminated block, internal identifier/separator/all-close
comment cases; the historical ordinary AST non-recovery/direct recovery distinction; full
Statement/separator CST node and token order; exact recovery kind/role/range/expectation/source order;
AST/direct cardinality, remainder, and losslessness; cfg(test)-only full `ParseLocal` snapshots with
non-default multi-frame state; and valid companion zero-candidate-helper proof.

Before changing any existing fixture, golden, diagnostic, or semantic expectation, apply
`rules/testing.md` expected-output protection. Only the already-approved comment-atomic difference
may change a corresponding ordinary expectation; every non-comment expectation remains protected.
Any other mismatch is a defect or a new approval question, not permission to update expected output.

Before the one package test, inspect its current inventory and resource profile under
`rules/testing.md`. The eight-process/ten-minute ceiling in §6 is a measurement budget, not a package
test time limit.

Do not run a workspace suite for this isolated gate, repeat the package suite after record-only
changes, or create a timing Cartesian product.

## 8. Rollback and stop conditions

Rollback or stop Gate 2 if:

- any ordinary accepted-path operation-ledger entry increases;
- ordinary valid behavior changes;
- any unauthorized non-comment recovery range, role, order, or boundary changes;
- the comment scanner violates its fixed lexical order;
- companion code becomes production-reachable before Gate 3;
- implementation needs another ordinary-loop extraction, general mode, shared dynamic abstraction,
  cache, replay, rescan, or allocation;
- static proof remains inconclusive after the assigned delta review;
- measurement would exceed §6's selected process/time budget, or the package test cannot be run
  safely under the current-inventory/resource controls required by `rules/testing.md` without prior
  approval.

Whole-binary size, wall-time, or RSS movement with a closed zero-work proof is recorded as
layout-sensitive evidence. It is not converted into a post-hoc allowance.

## 9. Operating mode and review budget

This amendment and Gate 2 use M2 because they change a durable performance/test contract around
shared parser recovery. For Gate 2 only, this section replaces the original four-fresh-reviewer
requirement with the current bounded delta-review rule:

- one implementer pass;
- `performance_auditor` for the semantic-work proof and bounded protocol;
- `spec_auditor` for exact recovery/companion/design conformance;
- the clean compiler and regression findings from the rejected duplicated-loop candidate carry
  forward only for topology, recovery, and test-contract regions unchanged by the new candidate;
- if implementation changes those carried-forward regions or exposes a new compiler/regression
  question, stop and reclassify the work rather than silently adding a third reviewer;
- at most two review/repair rounds, batching findings into one repair pass per round;
- progress/design synchronization as M0, with no extra code-review or test round.

No test, build, or performance run is part of drafting or reviewing this amendment.

## 10. Rejected alternatives

- Whole-process wall/RSS zero effect as the governing discriminator: both semantically clean,
  production-unreachable shapes failed it.
- Another static-specialization or general-loop variation: reopens the first failed shape and changes
  ordinary hot-path structure.
- An arbitrary slowdown/RSS allowance: post-hoc and contrary to the user direction.
- Crate/feature isolation: disproportionate architecture and bug surface.
- Another multi-hour certainty run: violates current policy and explicit user direction.
