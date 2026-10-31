# Sprint EFFECT-PERMISSION-PER-CALL-PUBLICATION / R52

Status: ADMITTED for a bounded per-call publication correspondence bridge.
Branch: `yulang3`; base commit `b8564a10bb6c10dfea61434441a73c718a3d927b`; use the existing WSL checkout only.
Authority: the continuing Rust/Lean effect-hygiene goal, R51 bounded pass, and the 2026-10-16 goal-driven sprint decision. No changed user objective or production authority.
This sprint changes no public API, accepted language semantics, ordinary forwarding behavior, or original parent claim.

## Original obligation and fixed outcome

The original Simple-sub A/B claims, quantifiers, source domain, and `SourceProblem.InferenceSoundness` remain unchanged and OPEN. R51 established a conditional finite publication model and separated observer failure from ordinary forwarding, but its model requires exact per-call `CallReads`, `DrainReads`, and `ModeReads` evidence that the current Rust observation does not fully retain.

Construct a private record for every actual Forward call, captured immediately around that call, sufficient to connect one checked plan index and one publication to its exact endpoint, upper operand, fact/occurrence/cause, pre-call origin and emission cuts, pre-call physical slot state, returned status, and only that call's new drain/completion/emission evidence. Preserve `AlreadyPresent` even with zero prior emission records. New per-call evidence remains best-effort: missing identity or observer allocation failure disables observation and cannot reject otherwise successful inference. Do not attribute an earlier or later call's records by equal occurrence/task/cause.

Success requires the independent reviewer to verify that Rust capture produces the exact per-call data needed by R51's model predicates, and that the Lean R52 construction uses the same call identity and cuts. A call record must be uniquely selected by `(publication identity, plan index)` before comparing endpoint fields. Repeated equal occurrence/task/cause calls, swapped plan indices, emissions from neighboring calls, missing completion, and allocation failure are the falsifiers.

## Exact lanes and leases

Rust author `/root/r52_rust`, at most 1,200 seconds, writes only:

- `crates/yu-solver/src/candidate_receiver.rs`
- `crates/yu-solver/src/candidate_context.rs`
- `tasks/agent-loop/inbox/effect-permission-per-call-publication-r52-rust.md`

Lean proof owner `/root/r52_proof`, at most 1,200 seconds, writes only:

- `notes/theory/lean/YulangClosure/PerCallResidualPublicationR52.lean`
- `tasks/agent-loop/inbox/effect-permission-per-call-publication-r52-proof.md`

Fresh independent reviewer `/root/r37_inventory_review`, at most 900 seconds, reads frozen code/model and returns its report; primary places it at:

- `tasks/agent-loop/inbox/effect-permission-per-call-publication-r52-review.md`

Primary owns this contract, admission/current/outcome records, leases, adjudication, Git and push. Children do not create teams. Read-only inspection is allowed for `crates/yu-solver/src/lib.rs` and the frozen R51/R50 Lean dependency cone. If exact attribution requires writing a producer outside the Rust leases, stop and report the required source change; do not edit `lib.rs` or enlarge a lease.

## Proof and implementation method

Rust must capture a pre-call cut immediately before each actual `constrain_live_effect` call and bind it to a unique local publication identity and original plan index. After a successful return, it may capture the corresponding completion and current physical evidence. The query must only inspect records admitted by that call's cuts; a publication-wide frontier or post-hoc occurrence/task/cause search cannot stand in for per-call identity. Keep all observation allocation and missing-evidence paths best-effort and preserve exact Forward order and arguments.

Lean must import R51's fixed model, define the per-call record relation, establish uniqueness/index and cut separation, and show the captured record instantiates the relevant `CallReads`, `DrainReads`, and `ModeReads` predicates under explicit source premises. It must preserve AlreadyPresent with zero previous emission, reject swapped/neighboring call evidence, and show observer unavailability does not imply failure of the corresponding Forward action. Apply the useful result back to the R51 source-correspondence gap; do not claim full extraction, runtime execution, subtraction, A/B, or whole-solver soundness.

## Frozen dependencies

Base HEAD: `b8564a10bb6c10dfea61434441a73c718a3d927b`.

- `candidate_receiver.rs`: `41272bf276761cdfe847264b4aaf0093d9feab361ca8d80881fd69ca86d449e0`
- `candidate_context.rs`: `c26a152e957980fcc844b7ff7145f712c4fd218b03415c50263e3dd81156c71f`
- read-only `lib.rs`: `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`
- R51 Lean model: `78a729b25e95812ba292c4e625ec69e46ff5eb70ff3ac2ae5b85dd1b33214d61`
- R50 Lean model: `4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2`
- R51 outcome: `dce798fe2270685b35b0d432b37905cdd66a487689a34a97406df0113dec7caf`
- R51 review: `5ee94d0574e12a03ec23ac71ef65cd860dfd658977d78b659169fe27b21e4bc5`

Authors must verify these hashes before writing and report drift. R51 review limits remain in force: raw stdout capture authentication is a separate receipt caveat; source/runtime completeness remains open.

## Resource and execution boundaries

Total budget: 4,200 seconds: Rust 1,200; Lean 1,200; independent review 900; primary 900 including 500 seconds closeout. Astra 0. Same checkout only. No build, tests, Cargo, Lake project build, formatter, target, cache, scratch file, new environment, worktree, service, or nested CLI. Lean may use only installed Lean 4.35.0 stdin audits, one CPU, `-M1024`, at most 120 seconds per process. Preserve exact commands, full theorem types/axioms, input/output bytes and hashes, diagnostics, and actual resource receipts. Do not inspect or delete quarantined paths.

## Review, checkpoint, and remaining scope

Review the frozen Rust/Lean artifacts after both authors STOP. Attack repeated equal calls, wrong/swapped index, wrong publication owner, old receipt, later emission, cut off-by-one, AlreadyPresent with zero old emissions, missing completion, and observer allocation loss. No open blocking finding may remain for a bounded pass. Only reviewed intended paths may be staged and pushed; use explicit paths and non-forced push.

Concrete execution, full source extraction, parent A/B, soundness, principality, termination, complete effect hygiene, and production remain OPEN regardless of this result. If per-call producer identity is not available within the exact leases, record the blocker and return the required path to Luna without claiming closure.
