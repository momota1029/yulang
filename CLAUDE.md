# Codex MCP operating policy

This repository uses Codex MCP as the primary implementation and investigation engine.

Claude's role is to supervise, constrain, review, decide, and unblock.
Claude should not compete with Codex by doing parallel repository investigation or implementation work.

In this policy, "Claude" includes Claude Sonnet 5 or any successor Claude model acting as the supervising agent.

Claude Sonnet 5 must not assume that its built-in knowledge of MCP is current, complete, or aligned with the Codex MCP implementation used in the current environment.
When MCP behavior matters, Claude must reason from the current environment, not from model memory alone.

## Hard rule: Codex MCP first

Claude must not inspect the repository before delegating to Codex MCP.

For any repository-related request, including simple file lookup or status checking, Claude's first repository action must be a Codex MCP call.

This rule applies to:

* simple file lookup;
* checking the current project state;
* finding relevant code;
* reading existing design notes;
* investigating test failures;
* understanding the current implementation;
* implementation;
* refactoring;
* diagnostics;
* deciding which tests or checks are relevant.

Claude may do only one thing before calling Codex MCP: visibly explain the intended delegation to the user.

Claude must not use repository-inspection tools before the first Codex MCP call.

Forbidden initial actions include:

* using `Read` to open files;
* using `Grep` or `Glob` to find relevant files;
* using `LS` to inspect directories;
* using `Bash` to run commands such as `ls`, `find`, `rg`, `cat`, `sed`, `git grep`, or similar inspection commands;
* reading existing documents or source files before delegating to Codex;
* doing the investigation itself and then asking Codex only to implement the result.

Instead, Claude's first repository action must be a Codex MCP call.

## Codex MCP visibility rule

Claude must never call Codex MCP silently.

Before every Codex MCP call, Claude must write a short visible note explaining:

* what task will be delegated to Codex;
* whether the task is read-only or write-enabled;
* the rough files, directories, or project area in scope;
* what result is expected from Codex.

This note must be shown before the Codex MCP call, not after it.

## Codex MCP sandbox and approval policy

Every write-enabled Codex MCP call must explicitly pass `sandbox: workspace-write` and `approval-policy: never`.

Every read-only Codex MCP call must explicitly pass `sandbox: read-only` and `approval-policy: never`.

## codex-flow plugin tool notes (environment-specific, discovered 2026-07-31)

The `mcp__plugin_codex-flow_codex__*` tools (`codex_execute`, `codex_continue`, `codex_review`, `codex_batch`) are a separate MCP surface from the base Codex MCP tool (`mcp__codex__codex` / `codex-reply`). They are useful as a fallback when the base tool's client-side idle timeout is a concern, since they expose an explicit `timeoutMs` parameter Claude can set directly (default 60 minutes, up to 2 hours) — the base tool's timeout is host/settings-level and not controllable via tool call parameters.

Practical notes for this environment:

* `codex_execute`, `codex_continue`, and `codex_review` default to opening a visible Terminal window (`terminal` param, defaults to `env CODEX_MCP_TERMINAL=1`). Always pass `terminal: false` explicitly unless the user asks to watch live progress in a terminal — otherwise a distracting terminal window spawns for every call.
* `codex_batch` has no `terminal` parameter at all (and did not spawn a terminal window in observed use) — no action needed there.
* None of these tools expose a separate `approval-policy` parameter. Proceed non-interactively as the tools are designed for; do not treat this as a policy gap requiring a workaround.
* `codex_batch` is well-suited for fanning out parallel work across distinct git worktrees (each task takes its own `cwd`) — useful for the kind of historical-commit comparison work described under "Sol-required tasks."
* These tools generate local operational artifacts under `.codex-flow/` (e.g. live logs) — this is gitignored; do not commit it.
* See `~/CLAUDE.md`'s "Codex への委譲" section for the general (cross-project) rule that the `model`/`reasoningEffort` tool-call parameters — not the `Model:`/`Reasoning effort:` prompt text below — are what actually select the model.

## Memory safety for large infer-crate test runs (discovered 2026-07-31)

An unscoped `cargo test -p infer --lib` (default parallelism, debug build) crashed the WSL2 VM twice during CDM-E verification, requiring a full WSL restart both times. Root cause: a debug-only cross-check (`debug_assert_qualified_carrier_index_matches_linear_scan`, introduced by CDM-B) was firing unconditionally on every claim-parent insertion, doing an O(n) linear rescan of `claim_parents_by_constraint` plus a fresh `FxHashSet` allocation each time — at the insertion volumes CDM-0 measured (hundreds of thousands to millions of calls across a full test run), this reproduced the same unbounded-rescan cost pattern CDM-A through D exist to eliminate, just relocated into the safety-net check itself. Fixed in `e76d70ca` (the check is now `cfg(test)`-gated and only invoked explicitly by the one test that needs it, not fired implicitly on every production-path insertion).

Even with that fixed, default to capping test parallelism for infer-crate (and any other large) test runs: pass `--test-threads=4` (or similar, well under this machine's `nproc` of 20) rather than leaving it unbounded, as a standing safety margin.

The user has explicitly declined a systemic WSL-level memory cap (`.wslconfig`) for this environment and is comfortable with the occasional crash as the tradeoff for not doing that extra setup. Do not re-propose that safeguard unprompted.

**Update (2026-08-02):** `--test-threads=4` alone is not sufficient once a real MPC/DPN performance regression is present (as opposed to the CDM-B debug-assert bug above, which is fixed). An unscoped `cargo test -p infer` with `--test-threads=4` still hung for 8+ hours and drove available memory down to ~900MiB before being killed — the `characterization`/`real_std`/`repository_std`-suffixed tests and `stage0`/`stage2`/`stage3`/`stage6` acceptance tests load the full std library and can each take minutes to hours if a solver-side regression is active. When verifying infer-crate changes under time pressure or suspected regression, explicitly `--skip` these heavy suites (e.g. `--skip repository_std --skip real_std --skip cprov_a --skip cprov_h --skip sound_a --skip stage0_characterizes --skip stage2_snapshot --skip shadow_dirty_oracles_characterize --skip stage6_`) and scope to the module under test (e.g. `cargo test -p infer --lib constraints::`) rather than running the full crate suite blind. Confirm the 4 known pre-existing failures (`urr_v3_co_owned_survivor_direct_root_does_not_reopen_replay_premise`, `general_subtype_failures_have_infer_analogs_but_carry_no_record_identity`, `subp_b_portable_exports_match_local_explanation_topology`, `pusp_a_characterizes_parameter_and_scheme_provenance_gaps`) are the only failures before treating a run as green.

**Incident (2026-08-02, RCPF-C3a verification):** Despite the skip list above already being written down, Claude ran `cargo test -p infer --lib lowering:: -- --test-threads=4` with NO `--skip` flags at all — reusing the mental model "this module doesn't need the constraints:: skip list" instead of recognizing that the heavy suite names (`stage0_characterizes`, `stage2_snapshot`, `shadow_dirty_oracles_characterize`, `stage6_`) live under `lowering::body::*`, not `constraints::`, and are therefore *more* directly hit by an unscoped `lowering::` run than by a `constraints::` run. Four of these ran concurrently under `--test-threads=4`, RSS hit ~30GB (91.9% of system memory, swap climbed to 3.7GB), and the user had to flag it ("メモリ92%．ヤバい") before Claude caught it and force-killed the process. Memory recovered immediately after `kill -9`. **Lesson: the full `--skip` list above is not module-specific — copy it verbatim into every `cargo test -p infer` invocation regardless of which submodule filter is used, never assume a different module name means the heavy suites don't apply.**

**Incident (2026-08-04, RCPF-F soak Phase 2):** Running the *entire* unfiltered `cargo test -p infer --lib` (no module filter, only the standard 9-pattern `--skip` list, `--test-threads=4`) — needed for the RCPF-F soak's "full infer test" workload category, since the soak explicitly cannot just skip everything — drove RSS to ~24GB (73% of system memory, MemAvailable down to ~5.8GB) within about 32 minutes of wall time, triggering a Monitor low-memory alert. The cause was four tests **not on the documented 9-pattern skip list** running concurrently for 60+ seconds each: `analysis::tests::case_03::cache_candidate_partial_option_1_slice_1_settles_ref_list_index_effect_head`, `lowering::body::stage0_tests::suffix_safety_stage0_paired_frontiers_are_characterized_before_generalization`, `lowering::body::yumark_tests::yumark_full_static_role_scans_stop_at_flat_format_selection`, and `lowering::tests::case_07::role_impl_conformance_parse_error_merge_is_blocked_before_actual_shape_projection`. Claude caught the low-memory Monitor alert and killed the process before it escalated (`SIGTERM`, then confirmed dead — memory recovered to 28GB available immediately). **Lesson: the 9-pattern skip list only catches the suites people have separately noticed were slow; it is not a complete inventory of every individually-heavy test in the crate. Any invocation that omits a module filter (i.e. actually runs the "full infer test" scope, as RCPF-F's soak requires) needs either `--test-threads=1` or active RSS monitoring with a kill-switch — do not assume `--test-threads=4` is safe just because the known 9 patterns are skipped, once the run covers modules beyond `constraints::`.**

## MCP version and implementation awareness rule

Claude must not rely on MCP protocol documentation or model memory alone when workflow correctness depends on MCP behavior.

This is especially important for Claude Sonnet 5, because Sonnet 5 may know some MCP concepts while still being unaware of the exact MCP version, Codex MCP behavior, host behavior, UI behavior, or current implementation gaps in the environment.

Claude must distinguish among:

* behavior defined by the MCP specification;
* behavior implemented by the MCP server;
* behavior implemented by the MCP client or host;
* behavior actually surfaced to Claude, the model, or the user;
* behavior implemented specifically by Codex MCP, which may differ from generic MCP behavior.

Claude must not assume that the following are supported, correctly wired, or user-visible merely because they exist in an MCP specification:

* `notifications/progress`;
* `notifications/message`;
* `tasks`;
* task status notifications;
* dynamic tool, resource, or prompt list-change notifications;
* draft or experimental MCP features;
* features introduced after the MCP version used by the current environment.

Codex MCP may not support the latest MCP specification.
Codex MCP may also support some MCP features internally without surfacing them to Claude, the model, or the user.

Therefore, Claude must treat MCP progress and logging support as environment-dependent.

When a task depends on MCP-version-sensitive behavior, Claude must require Codex to verify the current environment before relying on that feature.

Verification may include:

* checking the local Codex version;
* checking the local MCP SDK or protocol package version;
* inspecting generated schemas or available protocol capabilities;
* checking local Codex MCP documentation or configuration;
* running a small local smoke test when practical;
* reporting whether protocol-level progress is actually visible in the current host.

Claude must not block ordinary repository work on a full MCP conformance investigation.
The verification should be proportional to the task.

## Codex MCP progress reporting rule

Progress reporting is mandatory for long-running or multi-step Codex work.

However, Claude must not assume that Codex MCP supports protocol-level MCP progress notifications.
Claude must also not assume that protocol-level progress notifications, even if sent, are visible to the user.

A Codex MCP request must explicitly require progress reporting when the task involves any of the following:

* inspecting multiple files or directories;
* running tests, builds, diagnostics, or other commands that may take noticeable time;
* making implementation changes;
* diagnosing a failure whose cause is not already known;
* working through multiple slices of a larger task.

Claude must instruct Codex to use the best verified progress-reporting channel available in the current environment.

The preferred order is:

1. Use protocol-level MCP progress notifications if they are verified to work and are surfaced by the current host.
2. Otherwise, use normal textual progress output if the current channel can surface it during execution.
3. Otherwise, include a `Progress reports:` section in the final structured report, summarizing the milestones reached during the task.

Claude Sonnet 5 should treat this as an operational fallback rule:

* MCP progress is useful when available.
* MCP progress must not be assumed.
* Codex MCP may not support MCP progress.
* Lack of protocol-level MCP progress does not remove the progress-reporting requirement.
* If protocol-level progress is unavailable, Codex must still report progress textually through whatever channel is available.

Progress reports must be concise, concrete, and operational.

Codex should report progress at meaningful milestones, such as:

* after identifying the relevant files;
* after finding the likely cause of a failure;
* before making a write-enabled change;
* after completing a focused implementation slice;
* after running checks;
* before committing;
* when blocked or when the task has expanded beyond the requested scope.

Each progress report should state:

* what has been inspected or changed so far;
* what result, clue, or blocker was found;
* what Codex will do next;
* whether there are any risks, blockers, or scope changes.

Codex must not flood Claude with low-value progress messages.
Progress reports should be milestone-based rather than line-by-line narration.

Claude must not treat the final report as a substitute for progress reporting on long tasks when progress can be surfaced during execution.
If progress cannot be surfaced during execution, the final report must still summarize the progress milestones that occurred.

When Codex provides progress reports, Claude should relay meaningful progress to the user when it helps the user understand what is happening.
Claude should summarize progress in user-facing language instead of dumping raw logs, unless the user explicitly asks for raw logs.

## Role split

Codex MCP is the primary worker.

Codex should handle:

* repository investigation;
* file discovery;
* reading source files and design notes;
* implementation;
* refactoring;
* test-failure diagnosis;
* running relevant checks;
* producing focused local commits;
* reporting milestone progress through the best available channel.

Claude should handle:

* choosing the next task;
* constraining the scope;
* deciding whether the task should be read-only or write-enabled;
* deciding whether MCP capability verification is needed;
* reviewing Codex's report;
* inspecting diffs and test results after Codex returns;
* deciding whether another Codex call is needed;
* helping Codex when it gets stuck;
* pushing commits to the remote when appropriate.

Claude should not directly edit code unless an exception applies.

## Exceptions

Claude may directly inspect or edit the repository only when one of the following exceptions applies:

* Codex MCP is unavailable;
* the Codex MCP call itself fails;
* Codex is clearly stuck and needs Claude to inspect a narrow, specific point in order to unblock it;
* the user explicitly asks Claude not to use Codex;
* the user explicitly asks Claude to inspect or edit the repository directly;
* the relevant content is fully pasted in the conversation and no repository inspection is needed;
* the delegation would be pass-through (see below).

### Pass-through exception

A delegation is pass-through when Codex would make no decision that Claude has not already made.

If Claude has already determined the exact content to be written, the exact edit to be applied, or the exact command to be run, then handing that to Codex adds a round trip and no judgment. In that case Claude must do the work directly instead of delegating it.

Concrete signs a request is pass-through:

* the request body contains the full text to be inserted, verbatim;
* the request specifies both the target file and the exact string to change;
* Codex's only remaining work is to transcribe, paste, or run something already fully specified;
* the request would be routed to Luna under the model routing policy — Luna-tier work is, by definition, work whose correct output Claude already knows.

This exception does not apply when Codex must still locate files, verify current state, choose among options, or check that the change is correct. Those are real delegations even if the intended edit is clear.

Claude must not use a Codex call as a formality to satisfy the Codex-MCP-first rule. The rule exists to keep Claude from competing with Codex on investigation and implementation, not to insert Codex into work that requires none.

Even when Codex is stuck, Claude must not immediately take over the whole investigation.
Claude should first diagnose the blockage, narrow the task, and send Codex a more specific follow-up request targeting a smaller file, function, test, or diff.

If Codex MCP is unavailable or does not support progress reporting, Claude may continue under the relevant exception only after making that limitation visible to the user.

## Delegation prompt discipline

When Claude delegates work to Codex MCP, the request must be concrete, bounded, and operational.

Claude must not give Codex vague or open-ended prompts such as:

* "Investigate this."
* "Figure out what is going on."
* "Improve this area."
* "Refactor as needed."
* "Read the repository and decide what to do."
* "Find the best approach."

Claude must not delegate broad judgment to Codex unless the user explicitly asks for architectural exploration.

Every Codex MCP request must include:

1. Objective

   State the exact goal in one or two sentences.

2. Mode

   Explicitly state whether the task is read-only or write-enabled.

3. Scope

   Name the relevant files, directories, commands, tests, or project area when known.
   If the exact files are unknown, ask Codex to find only the minimum relevant files and stop after reporting them.

4. Procedure

   Give Codex a concrete sequence of steps.
   Prefer numbered steps over prose.

5. Environment and capability check

   When the task depends on MCP behavior, ask Codex to verify the relevant current-environment support before relying on it.

6. Progress reporting

   Require Codex to provide concise progress reports at meaningful milestones when the task is long-running or multi-step.
   Require Codex to state which reporting channel it will use.

7. Constraints

   State what Codex must not do.

8. Stop condition

   Tell Codex when to stop.

9. Required output

   Require a structured final report.

Claude must not ask Codex to "think freely" or "decide the best solution" for routine repository work.
Claude should make the judgment and give Codex a narrow execution task.

If Codex needs to make a decision that was not specified, Codex must stop and report the decision point instead of guessing.

## Required Codex MCP request template

Claude must format Codex MCP requests using this structure:

```text
Task:
<exact task>

Mode:
<read-only | write-enabled>

Sandbox:
<read-only | workspace-write>

Approval policy:
never

Scope:
<files/directories/project area; or "unknown, find the minimum relevant files only">

Steps:
1. <step 1>
2. <step 2>
3. <step 3>

Environment and capability check:
- If this task depends on MCP progress notifications, logging notifications, tasks, dynamic MCP notifications, or other MCP-version-sensitive behavior, verify whether the current Codex/MCP environment supports and surfaces that behavior.
- State which progress-reporting channel will be used: protocol-level MCP progress notifications, normal textual progress output, or final summarized milestone reports.
- Do not assume MCP protocol-level progress is supported or user-visible merely because it exists in the MCP specification.
- If Codex MCP does not support the relevant MCP feature, continue using the fallback reporting channel unless that limitation blocks the task.

Progress reporting:
- Progress reporting is mandatory for long-running or multi-step work.
- Use protocol-level MCP progress notifications only if they are verified to work and are surfaced by the current host.
- Otherwise, provide concise milestone-based textual progress reports through the normal available channel.
- If progress cannot be surfaced during execution, include a `Progress reports:` section in the final report.
- Report after finding relevant files, after identifying the likely cause, before write-enabled changes, after each coherent implementation slice, after checks, before committing, and whenever blocked.
- Record the task start time when work begins, and check elapsed time at every progress-report milestone.
- Each progress report must state what was done, what was found, what will happen next, and any risks or blockers.
- Do not send noisy line-by-line narration.

Constraints:
- Do not edit unrelated files.
- Do not perform broad refactors.
- Do not change public APIs unless explicitly required.
- Do not push to any remote.
- Do not force-push.
- Do not delete branches or rewrite history.
- Create small local commits for completed coherent slices.
- Report every commit hash and commit message.
- If pushing is needed, stop after committing and tell Claude that the commits are ready to push.
- Do not run expensive or networked commands unless explicitly authorized.
- If the task becomes larger than described, stop and report why.
- If an MCP capability needed by this request is unsupported or unverified, do not silently assume it; report the limitation and use the defined fallback when possible.

Stop condition:
<when Codex should stop>

Return format:
- Summary:
- MCP/environment capabilities checked:
- Progress reporting channel used:
- Progress reports (including elapsed time at each milestone):
- Files inspected:
- Files changed:
- Commands run:
- Tests/checks run:
- Commits:
- Result:
- Remaining risks:
- Blockers:
```

## Default delegation targets

Claude should delegate the following tasks to Codex MCP by default:

* finding relevant files;
* checking the current implementation state;
* reading existing design notes;
* identifying the right place to make a change;
* proposing an implementation plan;
* implementing the change;
* diagnosing test failures;
* deciding which tests or checks should be run;
* running relevant checks;
* creating focused local commits.

## Documentation site prose

Before writing or editing any prose page under `web/docs/`, Claude must read both `notes/style/japanese-writing-guide.md`, the base norm for orthography, formatting, paragraph construction, and argument construction, and `notes/style/writing-rhythm-guide.md`, the layered norm for page-layer assignment, the conflict-arbitration table, rhythm, English prose, and translation pairs.

These writing guides govern site prose only and do not apply to commit messages or agent-to-user conversation.

## Commit and push responsibility split

Codex MCP may create local commits.

Claude is responsible for pushing commits to the remote.

### Codex's responsibility

Codex should:

* make small, coherent local commits;
* prefer one commit per meaningful implementation slice;
* run the relevant checks before committing when practical;
* inspect `git status` and `git diff --stat` before committing;
* use clear commit messages;
* report each commit hash and commit message;
* never push to any remote;
* never force-push;
* never delete branches;
* never rewrite history.

Commits are checkpoints.
They should make Codex's work reviewable, reversible, and easy to bisect.

Default commit policy:

* Prefer one commit per coherent change.
* Commit after each meaningful implementation slice.
* Commit after a bug fix is complete and relevant checks pass.
* Commit before starting a risky follow-up change.
* Do not accumulate a large uncommitted diff across unrelated tasks.
* Do not mix formatting-only changes with behavioral changes unless explicitly requested.
* Do not commit generated noise, temporary files, debug logs, or unrelated edits.
* Before every commit, inspect `git status` and `git diff --stat`.
* Use clear commit messages that describe the actual change.

### Claude's responsibility

Claude should:

* review Codex's report after each Codex MCP call;
* inspect `git status`, `git log --oneline -n 5`, and `git diff --stat`;
* check the current branch and remote before pushing;
* confirm that the branch is appropriate for pushing;
* push regularly to keep the remote in sync, including directly to `main` — this repo's normal workflow is single-branch development on `main`, and per user instruction (2026-08-03: "基本的にバンバンpushしていい(普通に同期は取るべき)"), routine pushes to `main` do not require per-push confirmation;
* never force-push unless the user explicitly asks for it;
* report the pushed branch, remote, and commit hash after pushing.

Push rule:

Codex must not push.
If pushing is needed, Codex should stop after committing and report that the local commits are ready. Claude then performs the push as a visible supervisor action — routinely, without needing to ask first each time, since keeping the remote in sync is the expected default for this repo.

**Note (2026-08-03):** this policy previously required explicit per-push user approval before pushing directly to `main`. The user explicitly relaxed this ("CLAUDE.mdのpushルールは少し弱めてください") after noticing ~52 local commits had accumulated unpushed. The prior caution around protected-branch pushes is superseded by this note for this repo specifically; force-push and history-rewrite caution remain unchanged.

## Long-task slicing policy

Claude must size the task before choosing a reporting granularity. Applying the full slice-and-report loop uniformly is what drives Codex call counts up without a matching gain in safety, so small/low-risk work should not pay that cost.

### Small/low-risk tasks: single-pass execution

A task qualifies as small/low-risk when all of the following hold:

* it touches one file, or a small number of tightly related files;
* the cause or the target change is already known — no open-ended investigation is needed;
* it does not touch public APIs, type-soundness-relevant code, or a shared/production-critical path;
* a single check (test, build, or lint) can confirm correctness.

For a small/low-risk task, Claude may give Codex one request that covers investigation, implementation, the relevant check, and the commit in a single call. Codex should still report what it found, changed, ran, and committed, but as one final structured report rather than a multi-step live loop. The Codex MCP progress reporting rule still applies if the single pass turns out to take noticeable time.

### Large/risky tasks: sliced execution

A task requires slicing when any of the following hold:

* the cause is not yet known and requires open-ended investigation;
* the change spans multiple unrelated files or subsystems;
* the change touches public APIs, type soundness, or a shared/production-critical path;
* the blast radius of a wrong change is high or hard to reverse;
* the task is large enough that an uncommitted diff would become hard to review or bisect.

For a large/risky task, Claude should explicitly instruct Codex to work in small slices. Each slice should follow this loop:

1. inspect the minimum relevant files;
2. report the relevant files found and the next intended action;
3. make one focused change;
4. report what changed and any risks;
5. run the relevant check;
6. report the check result;
7. create a local commit;
8. report the commit hash and remaining work;
9. check elapsed time since the task started, then continue only if it is under 30 minutes and the next slice is clear.

Codex must not accumulate a large uncommitted diff across multiple unrelated changes.

If a task turns out larger or riskier than expected — including a task Claude initially classified as small/low-risk — Codex must stop and report the expansion instead of continuing silently. Claude should then re-classify the task as large/risky and switch to sliced execution for the remainder.

If protocol-level MCP progress is unavailable, long-task slicing still applies to large/risky tasks.
Codex must use textual milestone reports or final summarized milestone reports as the fallback.

## Elapsed-time limit for long-running Codex MCP work

The elapsed-time check is an additional stop trigger layered on top of milestone-based progress reporting and long-task slicing. It does not replace either policy.

Codex must record the task start time when work begins.
At every progress-report milestone, Codex must check the elapsed time since that start time and include it in the report.

Once elapsed time reaches 30 minutes, Codex must stop before starting the next slice or step and report the current state, even when the requested work is incomplete.
Continuing beyond that point requires an explicit decision from Claude as the supervising agent. Codex must not decide unilaterally to continue past the 30-minute limit.

## After Codex returns

After Codex returns, Claude must summarize:

* what Codex did;
* what MCP/environment capabilities Codex checked, if any;
* what progress-reporting channel Codex used;
* what progress Codex reported during the task;
* what files Codex inspected;
* what files changed;
* what commands Codex ran;
* what tests or checks ran;
* what commits were created;
* whether pushing is needed;
* what remains risky or unfinished.

Claude may inspect diffs and test results after Codex returns.
This review is for supervision and judgment only. Claude must not quietly take over repository exploration or implementation work that should have been delegated to Codex.

## If Codex gets stuck

If Codex gets stuck, Claude must not silently repeat the same request.

Claude should:

1. identify the exact blockage;
2. narrow the task;
3. reduce the scope to a specific file, function, test, error message, or diff;
4. give Codex a more concrete follow-up request;
5. ask Codex to stop and report again if the narrowed task is still ambiguous.

Claude may inspect a narrow, specific point only when doing so is necessary to unblock Codex.

If Codex is stuck because an MCP feature is unsupported, unavailable, or not surfaced, Claude should not keep asking Codex to use that feature.
Claude should switch the request to the fallback channel or narrow the task so Codex can proceed without that MCP feature.

## Summary rule

Claude must treat Codex MCP as the implementation engine.

Claude should not perform repository investigation or implementation before Codex.
Claude should not silently call Codex.
Claude should not give Codex vague freedom.
Claude should not push through Codex.
Claude should not let long-running Codex work proceed without progress reporting requirements.
Claude should not assume Codex MCP supports the latest MCP specification or surfaces protocol-level progress notifications.

The intended workflow is:

1. Claude explains the Codex delegation visibly.
2. Claude gives Codex a concrete, bounded request.
3. Claude includes MCP capability checks when the task depends on MCP-version-sensitive behavior.
4. Codex verifies the relevant current-environment capabilities when needed.
5. Codex states which progress-reporting channel it will use.
6. Codex investigates or implements in a bounded way.
7. Codex reports meaningful progress at milestones during long or multi-step work, using the best available channel.
8. Codex creates small local commits when changes are made.
9. Codex reports files, commands, tests, commits, risks, blockers, capability limitations, and progress milestones.
10. Claude reviews the result.
11. Claude pushes only when the branch and result are appropriate.

## Codex model routing policy

Claude is responsible for selecting the Codex model and reasoning effort before each new Codex MCP session.

Codex in this environment exposes three GPT-5.6 tiers — `gpt-5.6-sol`, `gpt-5.6-terra`, `gpt-5.6-luna` — from most to least capable and expensive. Reasoning effort supports `minimal`, `low`, `medium`, `high`, `xhigh`, and (Sol only) `max`. Routing is a three-way decision (Sol / Terra / Luna), not a two-way one; each tier has its own effort range below.

### Default model — Terra

Use `gpt-5.6-terra` with `model_reasoning_effort = "medium"` by default.

Terra is a capable model. Most repository work — locating code, reading it, making a bounded change, running the relevant checks, diagnosing a failure whose symptom is concrete — lands well within its range. Routing such work to Sol buys little and costs a lot, so Terra is the normal home for ordinary development work, not an exception carved out of a Sol default.

This default is safe because it is paired with the escalation rule below. The cheap-first-then-escalate loop is the intended mechanism for handling uncertainty: a task that turns out to need more judgment gets stopped and re-routed up, rather than being pre-emptively routed up on suspicion. Escalating one task occasionally is cheaper than running every task at the top tier.

Raise to `"high"` when the step is more involved than usual — a multi-file change, or a check result that needs real interpretation — and to `"xhigh"`, still on Terra, when it is bounded but unusually intricate. Try raising effort within Terra before considering a tier change.

Sol is reserved for the categories listed under **Sol-required tasks** — essentially, work that cannot fail locally. Outside those categories, prefer Terra even when the task is nontrivial.

When uncertain which tier fits, start at Terra and let the escalation rule move it up. Only skip straight to Sol when the task clearly matches a Sol-required category.

### Terra tier — everyday development work

Terra covers bounded work that needs real reasoning and tool use, including work that is not purely mechanical.

Terra is appropriate when:

* the objective is clear, even if the exact steps are not fully enumerated;
* the scope is bounded to a known area, even if the precise files must be found;
* the judgment required is local and reviewable, not architectural or semantic;
* a wrong result would surface through a check, a review, or an obviously odd report;
* the work does not fix a durable public interface or a design decision.

Typical Terra tasks include:

* locating a specifically named file, symbol, or string;
* finding the relevant files for a bounded change within a known subsystem;
* listing references or call sites;
* extracting explicitly requested information from known files;
* running specified commands or tests and interpreting their results;
* applying a local edit whose intent is decided but whose details are not spelled out;
* implementing a bounded change within one subsystem;
* diagnosing a failure with a concrete, reproducible symptom;
* performing mechanical formatting or notation normalization;
* converting supplied material into a fixed format;
* collecting bibliographic metadata or links from already identified sources;
* producing a preliminary draft from a complete outline and supplied content.

### Luna tier — mechanical, fully-specified, high-volume execution

Claude may use `gpt-5.6-luna` with `model_reasoning_effort = "low"` (use `"minimal"` for the simplest, most repetitive cases) only when the desired output is already fully determined before Codex starts, and Codex's job is purely to extract, transform, classify, reformat, or transcribe it.

Luna should be selected only when all of the following conditions hold:

* the exact shape of a correct result is already known and does not depend on any judgment Codex must make;
* the work is mechanical repetition or transformation applied uniformly across items, not investigation or synthesis;
* a wrong result is caught trivially and cheaply by a mechanical check (diff, exact-match test, format validator);
* the result either feeds into a subsequent Terra or Sol review, or is low-stakes enough that an error would have negligible cost.

Typical Luna tasks include:

* applying an already fully-specified find/replace or rename across a known set of files;
* re-formatting or re-indenting content into an exactly specified target format;
* extracting explicitly named fields from a known file into a list or table;
* running one specified command and returning its raw output unmodified;
* generating a commit message whose content and framing Claude has already dictated.

Luna must not be used for anything that requires the judgment described under Terra or Sol. If a task looks Luna-sized but requires picking among options, resolving ambiguity, or assessing correctness, route it to Terra or Sol instead.

Luna is bounded from below as well as from above. It applies to mechanical work that is nonetheless voluminous, repetitive, or spread across many files — enough of it that running it through Codex saves Claude real effort. It does not apply to a single fully-specified edit Claude could make in one tool call; that is a pass-through delegation and Claude must do it directly. See the pass-through exception under **Exceptions**.

The scale test: if the work is one edit, one paste, or one command whose output Claude already knows the shape of, do it directly. If it is the same fully-specified transformation applied across many sites, route it to Luna.

### Sol-required tasks

Use Sol XHigh for work that **cannot fail locally** — where a mistake is not contained by a test or a review, but propagates outward into everything built on top of it.

The distinction is blast radius, not effort. A bounded change can be wrong and simply get fixed; a design decision that is wrong is inherited by every later change, and by then it is expensive to undo. That second class is what Sol is for.

Sol XHigh is required for:

* architectural, API, type-system, semantic, or performance decisions;
* type-soundness work, and changes to shared or production-critical paths;
* open-ended investigation where the symptom is vague and the cause could be anywhere;
* mathematical reasoning, proof design, or proof verification;
* literature review, source comparison, novelty assessment, or research synthesis;
* drafting or restructuring papers, design documents, specifications, or other durable prose;
* refactors spanning multiple unrelated subsystems;
* reviewing the correctness of work whose failure mode would be silent;
* tasks where a plausible but shallow answer would be dangerous or expensive to discover later.

The test to apply: *if this is wrong, is it caught and fixed locally, or does it quietly become a premise for later work?* A hard but checkable task — a tricky implementation confirmed by a test — belongs on Terra. An easy-looking but globally load-bearing one — picking the shape of an API — belongs on Sol.

### Drafting distinction

Use Sol XHigh when Codex must decide any of the following:

* what the argument should be;
* how the document should be structured;
* which evidence should be included;
* how claims should be qualified;
* how conflicting sources or requirements should be reconciled;
* whether the draft is mathematically, technically, or rhetorically sound.

Terra may be used when the content and structure are already fixed and Codex is transcribing, formatting, shortening, expanding from an outline, or applying explicit editorial instructions. Luna may be used only for a narrower slice of that: literal transcription, reformatting, or fixed-template fill-in with no editorial judgment at all — not even shortening or rephrasing.

### Research distinction

Use Sol XHigh when Codex must determine what to search for, evaluate source relevance, compare claims, resolve ambiguity, synthesize conclusions, or identify missing evidence.

Terra may be used for bounded collection tasks, such as retrieving metadata, locating already specified material, or extracting requested facts from a known source set. Luna may be used only when the exact source and exact field to extract are both already named — no relevance judgment at all.

### Escalation rule

If Terra or Luna encounters ambiguity, unexpected repository structure, conflicting evidence, an unclear failure, or any decision not explicitly covered by the request:

1. Terra/Luna must stop rather than guess.
2. Terra/Luna must report what it found, what remains uncertain, and why the task is no longer mechanical.
3. Claude must start a new Codex session one tier up — Luna escalates to Terra, Terra escalates to Sol XHigh — unless the report already shows the task needs Sol-level judgment, in which case go straight to Sol.
4. The higher tier must receive the lower tier's report but independently verify important findings.

Do not repeatedly retry an ambiguous task at the same tier, and do not re-route a task Terra already found non-mechanical down to Luna.

### Quality-preservation rule

Routing down is bounded by verifiability, not by stakes alone.

Claude may use Terra whenever a wrong result would be caught by a check, a review, or an obviously incoherent report. The fact that output will be committed is not by itself a reason to use Sol — most commits are guarded by tests.

Prefer Sol XHigh when the result will be *relied on without further verification*: a design decision, a research conclusion, a published document, or a change whose failure mode would be silent.

Claude must not pre-emptively route up merely because a task feels important. Escalation exists for that; use it.

### Visibility

Before every Codex MCP call, Claude's visible delegation note must state:

* the selected model tier (Sol / Terra / Luna);
* the selected reasoning effort;
* whether the call uses the default Terra policy, a Sol opt-up, a Luna opt-down, or an escalation from a lower tier;
* one concise reason for the selection.

### Required request fields

Add the following fields to every new Codex MCP request:

```text
Model:
<gpt-5.6-sol | gpt-5.6-terra | gpt-5.6-luna>

Reasoning effort:
<minimal | low | medium | high | xhigh | max>

Routing classification:
<default Terra | Sol opt-up | Luna opt-down | escalated from <tier>>

Routing reason:
<one concise sentence explaining why the task is bounded and checkable, requires unverifiable judgment, or is purely mechanical transcription>
```

# 設計判断の優先順位と正本

## 優先順位

判断に迷ったら、次の順に従う。

1. ユーザーからの明示的な指示
2. ユーザー承認済みの署名付き設計文書（下記「設計文書の正本」）
3. この `CLAUDE.md`
4. 既存コードの設計意図・命名・テスト方針
5. 一般的な実装慣習

ただし、現在の作業範囲により具体的な指示がある場合は、それを優先する。

## 設計文書の正本

設計判断の正本は、ユーザー承認済みの署名付き設計文書である。

- 末尾に「著者: Claude (Fable 5)」の署名と「ユーザ承認済み」の記載を持つ
  `notes/design/` / `spec/` の文書は、設計判断の正本（authoritative）として扱う。
- 正本と他の文書（ChatGPT / Codex が生成した文書、無署名の note、古い spec）が
  矛盾する場合は、正本を優先する。
- 正本に書かれた意味論・決定・Rollback 条件を、実装の都合で変更しない。
  変更が必要に見えたら、実装を止めて正本へ戻り、ユーザーに確認する。
- 正本が対象とする挙動のテスト期待値は、正本の意味論から手で導出する。
  実装の現在の出力から逆算して書かない。
- 正本が spec 側の修正箇所を列挙している場合は、その指示に従って spec を更新する。

### Fable 5 不在時の起案担当

正本文書は本来 Claude (Fable 5) が起案する。Fable 5 が一時的に利用できない
場合の代替手順は次のとおり（2026-08-05、ユーザー指示に基づき確定）。

- Fable 5 が使えない状況で、Codex `gpt-5.6-sol`（xhigh）がその設計判断に
  必要な調査・検討をすでに行っている場合、**文書の本文自体を Sol に
  書かせる**。Sol は Sonnet 5 より上位のモデルであり、Fable 5 不在時の
  代役としては Sonnet 5 が要約・言い換えて書くより、Sol 自身に文章を
  書かせる方が文書の質が高い。
- この場合の Claude (Sonnet 5) の役割は、一次執筆ではなく
  **査読・検証・体裁の統一・署名**になる。Sol の草稿をそのまま正本へ
  コピーするのではなく、内容が既存の正本群（invariant、stop condition、
  用語）と矛盾しないか確認し、必要なら Sol へ差し戻してから確定する。
- 署名欄には両方の関与を明記する。例:
  `著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定`。
  Fable 5 起案時の「著者: Claude (Fable 5)」という体裁とは区別する。
- ユーザーは、Sol が書いた本文に対しても、Claude が書いた本文と同じ手順で
  承認できる——起案者が誰であっても、承認・正本化の手続きは変わらない。
- Fable 5 が復帰したら、この代替手順は使わない。通常どおり Fable 5 が
  起案する。

現在の正本:

- `notes/design/2026-07-02-resource-lifetime-decisions.md`
  （file / server 資源寿命の意味論 4 決定。決定4 は下記 §F7 により修正済み）
- `notes/design/2026-07-02-host-act-ffi-decisions.md`
  （host act FFI の意味論。unit 強制、tier、直交性規則、backend 非依存 host 契約）
- `notes/design/2026-07-02-speedup-proof-system.md`
  （高速化証明系の翻訳と評価。cert の質 A/B/C 分類と改善提案、承認済み）
- `notes/design/2026-07-02-static-route-promotion-plan.md`
  （静的 route 昇格の実装指示書。Stage 0 被覆率計測から。停止条件と
  「やってはいけないこと」を厳守すること。Stage 0 の実装位置と分類根拠は
  下記 2026-07-03 改訂により差し替え）
- `notes/design/2026-07-03-static-route-mono-resolution-plan.md`
  （静的 route 分類の mono 時再着床 指示書。分類の正本を specialize 側へ移す。
  evidence-vm 内 lowering 由来の分類（operation_static_route_resolution）は退役。
  L1 = task 内字句解決、L2 = SCC 縮約上の一回伝播。不動点反復禁止。
  2026-07-02 daily の Stage 0 数字は無効、Stage M1 で再計測・再判定）
- `spec/2026-07-02-io-resource-api.md`
  （file / connect / serve 統合仕様。型紙 = act + session + view + raw。
  close 系操作の追加は v1 決定への違反）
- `notes/design/2026-07-02-file-session-boundary-plan.md`
  （file public buffer 境界の実装指示書・改訂4・ユーザ承認済み。
  text_with pure mock parity の正規の解。scoped は state-passing プロトコル
  `f: str -> [e] ('a, str)`（貧者の存在型）、text_with は load/λ/store の 4 行。
  file_buffer act は unscoped の ambient 対だけ。転送・same_path・scoped 操作は
  存在しない。全 Stage 着手可。周辺 case の追加を本工事の代わりにしないこと）
- `notes/design/2026-07-27-my-visibility-enforcement.md`
  （`my` 可視性の統一 enforcement 指示書・ユーザ承認済み。D1 = `my` は declaring module と
  その子孫だけに見え、それ以外からはどの綴りでも届かない（Rust 規則）。述語は既存
  `ModuleNode.parent` を辿る `is_descendant_or_same` 一本で、direct path と `use` の両方が
  同じものを使う。子孫からの `use` は許可するので、private の出所を alias / glob / re-export /
  compiled namespace の全 copy site で持ち回る必要がある（1 箇所落とすと静かに漏れが復活）。
  compiled-unit format は 19→20。診断は `yulang.private-access` を新設。
  MYVIS-A〜F の 6 スライスで、provenance（A/B）を先に閉じてから可視性を有効化（C/D）する）
- `notes/design/2026-07-26-derives-clause-design.md`
  （`derives` clause の意味論と実装指示書・ユーザ承認済み。deriving は常に明示で、
  自動導出は持たない——role 解決が「適合候補ちょうど一つ」でしか成功しないため、
  自動化には impl 優先度機構が要る。3 attachment position（brace 後置 / `with:` 内 /
  宣言ヘッダ）、`via` は field delegation。v1 の derivable role は `Eq` と `Debug` のみで
  `Ord` は範囲外。DERIVE-A〜H の 8 スライス）
- `notes/design/2026-07-02-my-binder-sugar.md`
  （`\my &x ->` 束縛と `&do` の方向決定・ユーザ発案。with 系プロトコルの糖衣。
  実装は file slice の外の独立トラック。既存の `\&x` ref 束縛子は温存）
- `spec/2026-07-02-instant.md`
  （時刻値 instant / duration。epoch ナノ秒の純データ、取得は host act clock
  経由のみ。タイムゾーン・暦・単調時計は非目標）
- `notes/design/2026-07-03-contract-v1-stage2-closeout.md`
  （Contract v1 残り blocker 2 件の閉じ方・ユーザ承認済み・D4 追補済み。
  D1+D4: ambient は `file` act 内の ambient_touch / get / set
  （`file_buffer` act は消滅）。unscoped `file::text` の失敗は作成点で
  typed io_err（eager touch。missing は not_found、create しない）。
  公開型は spec §1 の `[file; io_err] ref '[file] str` と綴りまで一致。
  D2: discharge flush 失敗と out-of-protocol 直接 perform は
  `yulang.host-io-error` のまま（意図的な非対称）。
  D3: snapshot 系 raw-compat（open_text / open / open_in + private 8 操作）は
  退役。read_at / write_at は残す。file_session は post-v1 で Contract v1 の
  完成条件に含めない。Stage A（退役）→ Stage B（typed ambient）の順）
- `notes/design/2026-07-03-host-abi-v0.md`
  （host 実装 ABI 契約 v0 + band 注入要求スケッチ・ユーザ承認済み。
  Cranelift リンクを先に設計し VM 注入をその subset とする。
  HostOpFn / BoundaryValue / HostOutcome、symbol は manifest から決定的 mangling、
  grant の正本は runtime 層。ABI は v0 = 明示 unstable で、
  native 解封時の改訂は §10 の正規手続き）
- `notes/design/2026-07-03-host-manifest-compiler-production-plan.md`
  （host act manifest の compiler 生成移行 指示書・改訂1・ユーザ承認済み。
  ABI v0 文書の subset。正本は `pub host act` 修飾子の宣言側、
  registry は plan の manifest × ABI 登録集合。schema に column / hash / symbol。
  Stage 1 生成 → Stage 2 切替（前提 = ABI Stage α）→ Stage 3 は着手前に確認）
- `notes/design/2026-07-30-derived-row-claim-propagation-gap.md`
  （DCP-A〜E: replay claim propagation の契約決定・ユーザ承認済み（2026-07-31）。
  exact carrier による binary replay 両側継承、per-proof 投影（record-wide 禁止）、
  独立 exact carrier の proof ledger（§5.1 案D・§5.4 案C 確定）。conjunctive
  coverage token / Boolean proof 表現は意図的に先送り（stop condition §11.1-2）
  ——2026-07-31 の mixed-proof 文書がその継続設計）
- `notes/design/2026-07-31-mixed-proof-conjunctive-ownership.md`
  （mixed proof の連言所有と証明合成台帳（MPC）・ユーザ承認済み。DCP §11.1-2 の
  stop condition 発火を受けた別設計。claim 層（生成・継承・coverage・liveness・
  Qualified payload 計算）は不変のまま、record 単位の投影判定だけを Standalone /
  DerivedUnary / ReplayConjunction の節評価に置き換える。評価は memo 付き DAG
  一回走査で不動点反復なし、fail-open は正の証拠側。実装着手前に MPC-0
  （read-only 事前検証）必須、MPC-A〜E のスライスで進める）
- `notes/design/2026-07-31-claim-parent-delta-materialization.md`
  （claim-parent 登録の差分実体化（CDM）・ユーザ承認済み。`95b95586`（exact carrier
  を含む dedup key への修正）が顕在化させた性能 regression（std::text::parse module
  lowering が 6.126 秒→481.875 秒、約 78.66 倍）を閉じる設計。`95b95586` 自体の
  意味論・key は不可侵で、変えるのは処理量だけ。既存の `materialize_existing_target`
  による eager/lazy 区別を「全再走査」から「差分のみ」へ狭める。現行 bulk 再計算
  コードは削除せず test-only equivalence oracle へ退役。実装着手前に CDM-0
  （実測確認）必須、CDM-A〜E のスライスで進める。MPC-B 以降は CDM 着地後を推奨。
  CDM-A〜E は 2026-07-31 に着地済み（std::text::parse 481.875s→46.930s、約10.3倍）。
  五ケース characterization の `provenance_epoch` baseline は差分パスの粒度変化を
  反映して更新済み（`7085192b`、内容 hash は無変更）。SUBP/control-ir の4件failは
  triageの結果pre-existingと確認済みでCDM起因ではない）
- `notes/design/2026-08-01-derived-unary-premise-nodes.md`
  （DerivedUnary premise の証明ノード化（DPN）・ユーザ承認済み。MPC §12.1-7 の
  stop condition 発火（structural/reduction-route admission で DerivedUnary
  premise が構造的に解決不能）を受けた追補設計。premise の型を `BoundRecordId`
  単一から `Record`/`Constraint`/`RootCoverage` の多ソート `ProofPremise` へ
  一般化し、「解決」を登録時（lookup ゼロ）から評価時（既存 keyed metadata への
  O(1) OR 評価）へ移す。旧 D2-4 の Standalone fallback（誤分類の原因そのもの）は
  退役。MPC D2-5 を「derived claim ID 参照禁止・canonical root は対象外」と
  精密化（D6、ユーザレビュー時に要確認と明記された点）。実装着手前に DPN-0
  （read-only 事前検証）必須、DPN-A（登録層・挙動中立）→ DPN-B（評価拡張、
  MPC-C と同時 landing）のスライスで MPC-B/C の中身を差し替えて進める。
  DPN-0 実行済み（2026-08-01）: 証拠源分布・連鎖深さは合格、root claim
  アクセス経路で stop condition 発火（後継は下記追補文書））
- `notes/design/2026-08-01-dpn-root-claim-and-cycle-safety-addendum.md`
  （DPN 追補: root claim 到達性と評価サイクル安全性・ユーザ承認済み。
  著者は Claude (Sonnet 5)（Fable 5 が利用制限で一時利用不可のため、
  Codex Sol XHigh の調査・設計提案を統合して起案——正本文書の慣例からの
  例外として明記）。DPN-0 が発見した 2件のギャップを解消: (A) root claim
  への鏡 index `root_claim_by_producer_constraint` を Direct/Reduced 両方の
  生成元が通る共通コンストラクタ `original_upper_replay_claim` 一箇所で維持、
  producer→root 単射性を明示的 invariant 化。(B) 反証された arena 順序による
  停止性根拠を撤回し、pass-local な tri-color cycle guard へ置換（MPC の
  既存 Record cycle 規則を constraint ノードへ拡張するだけで新方針ではない）。
  DPN 文書は編集せず、§2-D3 source (c) と停止性根拠の後継としてのみ機能する）
- `notes/design/2026-08-01-urr-v3-causal-qualification.md`
  （URR v3: Direct claim の因果的 qualification・ユーザ承認済み。著者は
  Claude (Sonnet 5)（Fable 5 が利用制限で一時利用不可のため、Codex Sol XHigh
  の調査・設計提案を統合して起案——正本文書の慣例からの例外として明記）。
  DPN-B/MPC-C 着地（`df001de9`）後も motivating test
  `v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`
  が red のまま残った件の後継設計。原因は「reduced upper に同居する Direct
  Original claim が、同じ reduction の因果的下流にあるにもかかわらず無条件の
  独立 leaf として評価される」co-owned survivor ギャップ（2026-07-29 の
  unresolved item「URR v3」と同一）。DPN root base case の一文だけを、
  `ActiveCausalQualification(D, P, R)`（producer の exact
  `ClaimQualifiedParent` route・Reduced root 一致・co-location・liveness の
  4条件AND）が成立する場合だけ route 評価へ委譲する形に置換。MPC D3 の
  OR/AND、claim coverage/liveness payload、URR の generic replay 判定は
  不変。write-site 棚卸し・move 前後の snapshot 境界・invalidation edge
  配置・canonical root 再統合時の key 整合・複数 qualification の線形性の
  5点は D2.5 で未確定のまま実装 gate として残し、URR-V3-0（read-only
  事前検証）でこれを閉じてから URR-V3-A〜C のスライスへ進む。赤い regression
  `urr_v3_co_owned_survivor_direct_root_does_not_reopen_replay_premise`
  （`case_02.rs`、commit `0ae58f1d`）が pinned test。
  **2026-08-01 追記・結果**: URR-V3-A（登録層・挙動中立、`c4490082`）は着地・独立に有効。
  URR-V3-Bは実装するとpinned MPC control（`scheme_projectable_lower_keeps_only_independent_claim_on_mixed_record`）を
  誤って抑制する過剰一致が判明し、修正案（D1'、`RowRouteDependsOnProducer`）も
  本番トポロジーには届かない（producerにexact routeが無く、Bound/Constraint混在の
  provenance graphを新たに歩く必要がありD2.1のevent-local規律を超える）ため未commit・破棄。
  さらに本来の動機バグ自体は claim propagation 層と無関係と判明——motivating test
  `v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`のhand-built
  witnessが、LVB v5（`notes/design/2026-07-28-local-var-effect-boundary-fix.md`）自身の
  「nested callback parameterはbody lowering中fresh placeholder、concrete ref接続は
  第二段階applicationまで遅延」規則を破ってたのが根因。この構築を直すだけ（claim propagation
  側は無変更）で hand-built outer scheme が parsed outer scheme と完全一致し、
  動機バグは`a65655b2`で決着。詳細は文書本体の2026-08-01追記セクション参照）
- `notes/design/2026-08-02-mpc-dpn-projection-evaluation-round.md`
  （MPC/DPN 追補: projection evaluation round と atomic clause-link mutation
  batch・ユーザ承認済み。著者は Claude (Sonnet 5)。CDM着地（`5040bf07..7085192b`）
  後もstd::text::parse loweringが46.930s（元目標15s未達）で明示的にdeferされていた
  性能ギャップの継続調査から、MPC-B/C（DPN-A/B）導入後にSchemeProjectionEvaluator::
  eval_recordがself timeの84.61%を占め、CDM直後（44.466s完走）比13.5倍以上悪化して
  timeoutする新規regressionへ発展した件の対処設計。診断censusでevaluator起動回数Q
  の内訳を実測し、対処をA1〜A4の4層に分割。A1（exact duplicate先行判定）とA2
  （proof mutationのflat-gate比較）はMPC-B/Cの実装是正として新規文書なしで実装・
  検証・commit済み（`6ecf60e8`、`9328d043`）だが、A1+A2適用後も300秒timeoutが
  残り不十分と実測確認。本書はA3（同一snapshot/view内でのevaluator共有、
  projection evaluation round）とA4（同一admission eventのclause-link群を
  before/after各一回に畳むatomic mutation batch）の正式契約。cycle安全性は
  既存cycle test（`dpn_b_cycle_guard_cyclic_route_plus_independent_source_
  stays_projectable`）由来の反例を踏まえ、「cycle cutが一度でも起きたらそのround
  以降は共有を止めてfresh evaluatorにフォールバックする」規則で担保。A3/A4は
  独立にrollback可能な単位として設計。regression gate 11項目・stop condition
  14項目。既存MPC/DPN/DPN cycle追補の意味論は変更せず精密化のみ）
- `notes/design/2026-08-02-replay-claim-parent-factorization.md`
  （replay claim-parent relation の factorization（RCPF）・ユーザ承認済み。著者は
  Claude (Sonnet 5)。A1〜A4 + reverse-index索引化でstd::text::parse loweringを
  300秒超timeout→48.705sまで改善した後も「数百ミリ秒」という実用目標には
  遠く、局所最適化の上限は2〜4倍程度と判明（Amdahl上限試算で12秒程度が下限）。
  詳細censusで「証明層とtruth層の分離」仮説を実測により否定（exact clause
  847,758→semantic 844,415、圧縮率わずか1.004倍、ReplayConjunctionはexact=
  semantic完全一致）——真の増幅源はclaim-parent(5,042万件)とexact link(2,852万件)
  で、unique qualified carrier(878,089件)一件あたり平均57.42件のclaim-parentが
  生成されている。原因は総当たり自体(`L<:α<:U`から`L<:U`を導く必要性)ではなく、
  「同じendpoint parent集合が多数のexact carrierへ物理コピーされている」という
  joinの非正規化——CDM設計文書が§5.3で「blast radiusのため先送り」していた
  exact-occurrence/summary分離の再開に相当する。採用する完成形はB(exact
  occurrence + immutable parent-set snapshot)+C(consumer別summary)の一体設計。
  exact carrier identity(`pivot/lower/upper/rule`)は一切粗化しない。RCPF-0
  (追加census)→A(shadow ledger)→B(dual-write oracle)→C(evaluator切替)→
  D(upper claim切替)→E(clause-link切替)→F(flat ledger撤去)の6段階、各段階
  独立commit・独立rollback可能。correctness invariant 23項目・stop condition
  16項目・棄却案14件(carrier key粗化、live endpoint参照、semantic dedupのみ等、
  いずれもcensus実測により根拠付きで却下)。性能目標は正直に段階化——RCPF-F後の
  最低成功条件は24秒以下またはbaseline比2倍改善、中間目標15秒、製品としての
  最終目標0.5秒だが「B+Cは0.5秒到達を保証しない」と明記。届かない場合はlower×
  upper region化やlazy pivot solverを次の設計対象とする。
  **2026-08-02追記・admission順の意味論確定**: RCPF-0 censusで、representative
  claim(`coverage_root -> representative_claim`)にfirst-admission順を一体化
  すると圧縮率15.52%まで悪化し§12.3目標(10%未満)をFAILすると判明。RCPF-0bで
  「global (result,root) default + carrier override」案も検証したがoverride率
  95.37%で「疎」の前提が崩れ12.05%でFAIL。診断品質(portable provenance)への
  影響を精査した結果、診断コードが`claim_parents_by_constraint`を直接列挙する
  箇所は無く(`explain.rs`のexplanation graphはcategory順/edge順の別レイヤー)、
  診断が依存するのは「representative claim選択の結果」のみと確認。よって
  「representative claim選択は既存admission順ロジックのまま行い、結果
  (`coverage_root -> representative_claim`という順序を含まない有限写像)だけを
  永続化する」設計を確定(RCPF-0実測で8.27%、PASS)。§1.1/1.2/2.6(新設)/4.7/
  6.2-6.4/6.6/6.8/8.8/10(invariant 23新設「Diagnostic order isolation」)を
  改訂。A1〜A4とは別に、admission順・representative claim・portable
  provenanceに一切触れない安全な最適化として`flat_fail_open`用のclaimed-support
  attribution index(`00297d8f`)を先行実装し、45.228sまで改善（支配要因は
  HashMap insert/contains_keyに移行、RCPF本体実装が引き続き必要））
- `notes/design/2026-08-02-rcpf-quarantine-retry-authority-addendum.md`
  （RCPF追補: factored replay quarantine時のproduction authority・ユーザ承認済み
  （2026-08-02）。著者はClaude (Sonnet 5)（Fable 5一時利用不可のためCodex Sol
  XHighの調査・設計提案を統合して起案）。RCPF-C(evaluator切替)着手前に必要
  だった未決定事項——`ReplayFactoredShadowStatus::Failed`発生時のproduction
  挙動——を埋める。決定: RCPF-C〜Eではcompilation attempt単位(record/query単位
  ではない)でreplay read authorityを`Factored`か`LegacyRollback`の一つだけ選ぶ。
  `Failed`が起きたattemptは丸ごと破棄しlegacy-onlyでclean retry、retry不能なら
  hard error(confirmed-path fail-openは絶対にしない)。C〜Eでのretryは正常
  カウントせずRCPF gateの成功条件から除外。RCPF-F(legacy ledger物理撤去)の
  着手前提に「C〜E soak期間中organic `Failed`発生数ゼロ」を追加。23 invariant
  全部との照合済み。RCPF本文は未編集、本書が§11 C/D/E/F節への参照として機能)
- `notes/design/2026-08-03-rcpf-d-materialization-projection-addendum.md`
  （RCPF-D追補: upper claim materialization/lower projectionのfactored化設計・
  ユーザ包括的事前承認済み（2026-08-03、外出前の「進めます．全ての権限を許します」
  という包括的指示に基づく——通常の個別承認とは異なる例外として本文に明記）。
  著者はClaude (Sonnet 5)（Codex Sol XHighの調査・設計提案を統合）。RCPF-C3d
  production cutover(`a52dfd44`)着地後、RCPF-D実装(単純なread-side swap)を
  試みたところ282行のprototypeで scope-creep stop conditionが発動し安全に撤退、
  3点の追加設計が必要と判明: (1) `first_parent_by_root`にresult-local unordered
  index(`first_parent_roots_by_result`)をsibling追加、(2) 同一admission event内で
  factored summary commitをmaterializationより前へローカル並べ替え、(3) C3d後は
  evaluatorがFactored sourceを読むため、legacy mutation(Phase A、常に無条件)→
  factored commit+health(Phase B、これ以降だけgate)→factored依存derived
  mutation(Phase C、health成功時のみ)の3段階分離とdeferred publication fenceが
  必要(単純な順序入れ替えだけでは不完全なfactored stateを観測してしまう)。
  実装はD1(index追加)→D2a(qualified-parent publication分離)→D2b(clause-link
  publication分離)→D2c(summary delta+同一event順序)→D3a(upper adapter+shadow
  oracle)→D3b(lower adapter+shadow oracle)→D4(authority cutover)の7スライス、
  各150〜200行以内目標。23 invariant全部との照合済み。D4には2つの明示的
  stop gate(LegacyRollback下でのepoch列再現、historical root orderへの
  consumer-visible依存なし)。RCPF本文は未編集、本書が§11 D節への参照として機能。
  なお同日、C3d着地後の実測でstd::text::parse loweringは55.000秒(むしろRCPF-A期
  46.990〜48.705秒より微増)——C1〜C3dはread側のみの切替でlegacy write
  (claim_parents_by_constraint、約5000万行相当)は未削減という仮説をCodexが
  確認済み。write側削減はRCPF-D/E/Fまで進まないと効果が出ない設計だった。
  **2026-08-03追記(D2c実装中の発見)**: D2c実装が当初net+295行に達しscope-creep
  stop condition発動→破棄→D2c-1(summary delta+Phase A/B fence、net+108行)へ
  縮小して再実装(`141faef2`)、直後に発見された二重呼び出しバグ(Phase A新設の
  clause-link呼び出しと既存のmaterialization内呼び出しが最大3回重複)も追加修正
  (`70c9a12b`)。この過程でD2c-2として先送りされていた「post-consumer oracle
  failure時のmaterialization publication抑制」を調査したところ、これはtest-only
  oracleの理論的ギャップではなく、**実際にrelease buildで到達可能なproduction
  gap**と判明: `apply_scheme_projection_mutation`内のFactored evaluator(C3d由来)
  がfactored read failureを起こしshadow statusをFailedにした後も、同じ関数内で
  inclusion/owner/global/provenance epoch publicationが継続してしまう経路が残る
  (C3aのwhole-attempt discardで最終的な正しさは保たれるが、§3.3の「health
  decision失敗後はafter-round/publicationをしない」という精神には厳密には反する)。
  対処はD2c-2a(Phase B内でのclause projection完結、bounds.rsのみ約60〜100行)→
  D2c-2b(`apply_scheme_projection_mutation`の評価/publish分離、mod.rsに波及、
  約100〜150行——RCPF-D addendum元来の「mod.rs不変」制約から逸脱)→
  D2c-2c(event-local fence配線、bounds.rsのみ約100〜150行)の3段階に分割して進行中。
  **2026-08-03追記(D2c完了・D3a着手時の発見)**: D2cシリーズ(D1/D2a/D2b/D2c-1/
  D2c-2a/D2c-2b/D2c-2c-1/D2c-2c-2a/D2c-2c-2b)は全9commit完走、着地
  (`e8b17077`〜`fd516b24`)。続くD3a(upper materialization adapter+shadow
  oracle)着手時、正本文書自体が想定していなかった構造的ギャップを発見:
  replay parentとstructural/reduction parentが同一rootを取り合う場合、
  現在の設計(D1のresult-local summary index、C1のnon-replay flat facade)
  だけでは、legacyのfirst-admitted lineage(admission順で実際にどちらが
  先に承認されたか)を再構築できない——replay側はReplayResultSummaryの
  witness、non-replay側はC1のVecと、別々の索引に分かれていて、両者間の
  相対的なadmission順を保持する仕組みがない。invariant 23
  (admission順を永続化しない)を守ろうとした結果生じたgapで、
  「回避策で隠さず、signed addendum改訂なしに実装しない」として安全に
  停止(shadow-onlyのadapter primitives`e323929d`は安全なのでcommit済み、
  oracle wiring+mixed-kind assertionを含む診断コードはstash保存
  (`stash@{0}`、"WIP on main: e323929d refactor(infer): add upper
  materialization lineage adapters"のメッセージで検索可能)、作業ツリー
  には戻していない)。D3b/D4のmixed replay/non-replay stop gateにも
  同じ問題が波及するため、D3a以降の完成にはcross-kind representative
  選択の新設計(例: Phase Aで全parent kind横断のfirst-winnerだけを
  記録するorder-free sibling map)が必要——RCPF-D addendumへの追加追補
  として検討中)。
  **2026-08-03追記(D3a完走・D3b着手時に発見、より深いstop condition)**:
  cross-kind representative選択の追補(RCPF-D addendum§9、commit
  `87afed20`)を経てD3a-0a(`fb48c975`)・D3a-0b(`5f4e03db`)・D3a本体
  (`f72e0df3`)は無事着地——同一rootをreplay/non-replay parentが
  取り合う場合の勝者選択は解決した。ところがD3b(lower projection
  adapter)着手時に**さらに一段深いgap**を発見: 今度は同一root内の
  勝敗ではなく、**異なるroot間の相対的なadmission順**——legacyの
  `scheme_projection_claims_by_lower_record`/
  `projection_proofs_by_lower_record`は、mixed replay/non-replay
  historyで実際のadmission順(例: `NonReplay(root_b) → Replay(root_a)`
  と`Replay(root_a) → NonReplay(root_b)`)によって最終proof vectorの
  並びが変わるが、factored側(D1 summary + C1 non-replay facade +
  D3a-0a/0bのcross-kind winner map)は最終状態が同じである限りこの
  root間の順序を再現する手段を持たない。point queryやcanonicalな
  sort・固定kind優先度では再現できない、admission順の正規履歴問題。
  Solに「この順序は本当に診断・provenance品質に影響するuser-visibleな
  ものか、それとも単なる実装詳細か」を独立調査させた結果、
  **load-bearingと確定**(過去のSUBP-H実運用事故と同種)——
  `generalize/provenance.rs`のgeneralized witness edge順、
  `explain.rs`のappend-only insertion順+depth-first preorder契約、
  `portable_explain.rs`のportable snapshot順(budget truncationの
  prefixが変わる)、`crates/yulang/src/source/mod.rs`の`lower_sites`
  順(重複spanのfirst-cause選択に影響)の4箇所が、全て実際にこの
  順序に依存していることを確認済み。これは単なる実装スライスでは
  なく、「canonical ordering boundary」という新しい正規化設計
  (claimed parentをstable root/source keyで、independent supportを
  stable carrier keyで並べる等)が必要な、根本的な設計判断——
  historical admission順の永続化はinvariant 23違反になるため、
  legacy/factored両経路が同じcanonical順を使うよう揃える方向で
  検討する必要がある。RCPF-D3b/D4はこの正規化設計が承認されるまで
  ブロックされる。ユーザーの直接確認を経ずに実装まで進めるべき
  重さではないと判断し、read-only調査の結果を記録した上でD3b/D4を
  一旦停止した)。
  **2026-08-03追記(§10解決・ユーザ承認)**: ユーザが「これは進めた方が
  よいと思います」と明示的に承認し、canonical ordering正規化設計を
  §11として追記(未commit→本行の後にcommitされる想定)。決定: claimed
  supportはcoverage root昇順、independent supportはcarrier identityの
  完全total order(variant rank+payload)。legacy側の唯一のwriter
  (`update_scheme_projection_proofs`)へbinary search+canonical位置
  insertionを導入(read-time sortは不採用、hot path性能を守るため)。
  **最重要の発見**: これはRCPF cutoverと無関係な既存legacy挙動の変更
  ——duplicate-span survivor選択や主diagnostic spanまで変わりうる。
  実装はD3b-0a(canonical key primitive)→D3b-0b(projection permutation
  oracle)→D3b-0c(portable/truncation/diagnostic oracle)→D3b-0d(legacy
  canonical ordering cutover、factored adapterを含まない独立behavior
  commit、既存pinned testの意図的レビュー必須)→D3b-1(factored adapter)
  →D3b-2(full/delta oracle)→D4の順。D3b-0d着手前にユーザーへ改めて
  確認する、と正本に明記済み)
- `notes/design/2026-08-10-generalized-witness-claim-bridge-provenance-gap.md`
  （generalized witness の claim bridge provenance 欠落修正設計（GWCB）・
  ユーザ承認済み（rev.1: 2026-08-10、rev.2: 2026-08-11、closeout: 2026-08-11）。
  著者は Claude (Sonnet 5)（Fable 5 一時利用不可のため、Codex Sol XHigh の
  調査・設計提案を統合して起案）。general_subtype/pusp_a/SUBP-B の診断
  provenance 欠落を修正。claimed projection proof の識別を raw audit identity
  （bound, raw support, raw clause）と正規化 semantic certificate key
  （coverage_root 正規化）へ分離する `ClaimedProjectionProof`
  （Standalone/DerivedUnary/ReplayConjunction）と `GeneralizationParent` 新
  variant（boxed）を導入。rev.1 の「全 true OR arm」契約は Ω(A) 性能下界で
  詰み、rev.2 で「単一 decisive arm」契約へ縮小して着地。explain.rs の
  traversal を ExpansionView/TraversalWorkItem で再設計し、raw/filtered view の
  cycle 検出を分離。GWCB-0〜E 全スライス完了、motivating test 2件 green、
  性能は cold reproduction で pre-GWCB baseline 圏内へ回復（残差は GWCB 由来
  ゼロと bit-for-bit call-volume 比較で確認済み、既存 qualified-parent
  full-bucket sort hot path のばらつきと判明——後継は PCLF）
- `notes/design/2026-08-11-projection-clause-link-factorization.md`
  （projection clause-link relation の factorization（PCLF rev.3）・
  ユーザ承認済み（rev.1/rev.2: 2026-08-11、rev.3: 2026-08-11）。著者は
  Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読・確定
  （Fable 5 一時利用不可のため代替手続き）。GWCB closeout 後に見つかった
  qualified-parent admission クラスタ最適化（27〜32%改善、`0e208ab4`）に続く、
  projection-clause admission（parse self-time 約35%）の後継設計。
  28,526,006件の exact link が実は 847,858件の distinct clause しか無く、
  平均33.64件が同じ clause を物理重複している（RCPF型の非正規化）と実測
  confirm。record-local な `ProjectionFormulaBucket`
  （clause entry・support group・compact incidence index）への一本化を設計。
  rev.1 は claimed source template を clause entry 単位で仮定したが、Sol 自身
  による adversarial review で反例（同じ clause に異なる
  ReplayConstraint/ReplayEvidence の result が異なる incidence から到達しうる）
  が発覚し FAIL、rev.2 で source metadata を exact incidence 単位
  （`ProjectionIncidenceMetadata`）へ訂正。PCLF-0〜C は `b0d2a1a2` まで着地
  （membership/clause authority cutover 済み、footprint は当初報告の36.34%が
  計算誤りと判明し正しくは47.9024%——50%gateはmarginわずか2.1ポイントで通過）。
  続くPCLF-D（evaluator/GWCB cutover）は3回の実装試行が全てparse性能gateに
  違反（+14.4%/+10.94%（footprint gate 56.40%で二重違反）/+20.02%、いずれも
  correctness parityは完全）——原因をコード読解の複雑度推論だけで3回外し続けた
  末、gdb profilingで真因確定（per-item metadata accessではなく、rev.2の三
  category Vecを全support groupへcategory×support groupの入れ子で走査し、
  emptyな組み合わせまで訪問するnested `Map->Fuse->FlatMap` iterator topology
  自体が dominant cost。evaluator self-time proxyがPCLF-C比3/15=20.0%から
  borrowed-view attemptで6/18=33.3%まで増加、metadata lookupにはsampleゼロ）。
  rev.3でnon-empty runだけを保持する`canonical_runs: Vec<CanonicalProjectionRun>`
  ＋明示cursorへ設計変更、独立adversarial reviewでHIGH（decisive incidence
  identityのevaluator memo越え伝播——実装は3試行とも既に正しく動いてたが文書化
  漏れ）・MEDIUM（single runに全リンク集中時のwriter costがquadratic累積に
  なりうる懸念、明示的な計測・stop gate追加）を検出・修正済み。27 invariant・
  24 stop condition。
  **2026-08-11〜12完走**: PCLF-D0実装中に、design docのstop conditionが
  1,800件連続singleton admissionでN(N-1)/2の真正quadratic writer costを検出
  （ユーザ判断で構造的に塞ぐ方針を選択）——固定128-entry chunk+安全な
  arena-indexed AVL木（unsafeなし）へ再設計し、独立review 2回でHIGH（commit時
  key昇格がcapacity preflightから漏れatomicity違反）・MEDIUM（adjacency count
  の全support group走査、design不変条件違反）を検出・修正。PCLF-D1
  （evaluator/GWCB cutover本番）はevaluator self-time proxyがPCLF-C比
  20.0%→6.7%まで改善（3回の旧attemptの33.3%より大幅改善）、独立review 2回で
  HIGH（`Standalone`embedded/outer support不一致でdecisive-arm選択がlegacyと
  食い違う実バグ）・MEDIUM 2件（project_lower preflightの未移行、error
  precedence相違）を検出・修正。PCLF-E（legacy storage撤去）でfootprint
  legacy比32.1%（dual-write解消後）、cold parse 75.126秒（GWCB以前baseline
  約103秒から-33.7%）。PCLF-F closeoutでfull safety-scoped suite未完走
  （既知red以外の新規failureなし）を明記して区切り。着地後、ユーザの
  「劇的に重い何かが居る」という指摘を受けた再profiling調査で
  `try_prepare_projection_support_mutation`のfull-bucket snapshot
  clone-before-no-op-check（21.87M呼び出し中90.72%がno-opなのに毎回clone、
  累計23.5億要素）を発見・修正（`1cd46e86`）、続けてqualified-parentの
  first-source temporary over-reservation修正（`acdd4246`）。最終cold parse
  68.571秒（baseline比-33.7%）、RSS 7.81GiB）
- `notes/design/2026-08-12-qualified-parent-replay-occurrence-factorization.md`
  （qualified-parent replay occurrence relationのfactorization（QORF rev.3）・
  ユーザ承認済み（2026-08-12）。著者はCodex gpt-5.6-sol（xhigh）が起案、
  Claude (Sonnet 5)が独立査読・確定（Fable 5一時利用不可のため代替手続き）。
  PCLF closeout後、ユーザ指摘を受けた再profilingでqualified-parent key
  insertion（parse self-time約25〜31%）が新たなdominant clusterと判明——
  50,420,613件acceptedのうち99.812%が本物の新規fact（duplicateではない）。
  "-0" exact parity census（2026-08-12）で、qualified-parent replay entries
  50,390,357件とRCPFが既に保持するreplay occurrence ledgerのparent entries
  50,390,357件が完全一致（missing/extra/field mismatch全てゼロ）と確認、
  同じrelationの物理的二重保持と確定。RCPF occurrence ledgerをreplay
  qualified-parentの正本へ昇格させ、structural/reduction-route 30,256件
  だけ小さい別storeに残す設計。gap A（exact membership）はPCLFで検証済みの
  chunked AVLパターンを再利用、gap B（canonical順序がoccurrence物理層の
  admission順と一致しない）はoccurrence単位のcompact "canonical replay arm"
  projectionで解決。独立adversarial review 2ラウンドで、rev.1のHIGH 2件
  （occurrence単位の最小parent圧縮がmaterialization consumer——
  merge_structural_claim_parents等——には不十分でroot単位の代表parent
  projectionが別途必要と判明／統合transactionが現行のzero-accepted-parent
  でもevent記録される契約を見落としてた）と、rev.2のHIGH 1件（失敗時は
  event記録するがinner transactionはall-or-nothingという、現行動作との
  整合性が取れてなかった）を検出・修正。QORF-0（census）実施済み、
  QORF-A〜Fのスライスで進める。28 invariant・25 stop condition。
  性能見込み: RSS -2.0〜2.8GiB、parse 8〜18%改善（stretch 20〜25%）。
  **2026-08-11〜12完走**: QORF-A(shadow test型・レビュー省略、`9f76d676`)→
  QORF-B(shadow side index+統合prepare transaction、`13d18621`)は独立review
  でMEDIUM 2件（新規shadow構築のinfallible allocation／test-only writerが
  side shadowと不整合）を検出・修正（`b39ae324`）。QORF-C(occurrence side
  read authority cutover)は`c44e4cdd`着地後、独立reviewでMEDIUM 1件
  （design §8が必須と定めるexhaustive full-std parity gateが未実装）を検出、
  `075e5f83`で追加・実測0/50,390,357件一致で確認。QORF-D0(shadow occurrence-
  arm+root-winner projection、`9e2da9f0`)は独立reviewでHIGH 2件——(1)replay
  root-winner prepareのinfallible allocation、(2)arm rekey時にsingleton chunk
  がarena上でorphan化し物理footprintが際限なく成長する再発quadratic worst-case
  （PCLF-D0で一度構造的に潰したのと同じクラス）——を検出、ユーザの「受け入れず
  構造的に直す」という既定方針どおりchunk再利用で修正（`6042260e`）。QORF-D1
  (evaluator/materialization consumer cutover)はexhaustive parity 0件一致で
  正しさは確定したが、性能が実際に退行（parse +3.27%/full lowering +2.81%、
  3回ずつのcold run範囲が非重複で確認、baseline自体が66〜79秒とブレる中でも
  再現性あり）。2回のgdb実プロファイリングで、最初に疑ったk-way association
  cursor heapは否定（association bootstrap self-timeはむしろD1の方が低い）、
  代わりに見つけた本物だが不十分な最適化（cursor構築時の固定AVL stackを
  `MaybeUninit`化、約2.2M回の構築で536MiB分の無駄な初期化を排除）を適用しても
  ギャップは埋まらず。ユーザに退行を受け入れてQORF-E（legacy撤去）まで
  持ち越すか判断を仰ぎ、「既知の退行として一旦commit」の指示で`03aeaff5`+
  `6470e88f`として着地（設計書に数値・仮説・deferral理由を明記）。QORF-E
  (legacy replay qualified-parent storage撤去、`091cf4e2`)で、D1の退行は
  完全に解消されただけでなく§9のstretch目標（20〜25%改善）にも到達——D1
  baseline中央値比でparse -24.788%・full lowering -24.043%、QORF-C比RSS
  -4.343GiB（median 4.097GiB）。独立reviewはfindingsゼロ。QORF-F closeout
  （`df7fd0df`+`f6eef554`）で最終集計: pre-QORF baseline比でparse -17.19%・
  full lowering -25.50%・RSS -45.01%。exhaustive parity全工程で0/50,390,357
  件一致を複数回確認、correctnessは一貫して完全。safety-scoped suiteは
  PCLF-F同様に部分実行（768 passed/1 known-red/2 ignored/490 unfinished、
  新規failureなしを確認した上で区切り）。QORF-A〜Fの一連で、独立reviewが
  ほぼ全ての本番書き込み経路スライスで実バグを検出——このプロジェクトの
  「shadow構築→independent review→修正→commit→push」という反復パターンが、
  今回も繰り返し機能したことを示す）
- `notes/design/2026-08-12-cpk-preflight-structural-validity-addendum.md`
  （CPK追補: projection preflightの構造証明とsnapshot-scoped validity reuse・
  ユーザ承認済み（2026-08-12）。著者はCodex gpt-5.6-sol（xhigh）が起案、
  Claude (Sonnet 5)が独立査読・確定。QORF-F closeout後、ユーザ指摘の
  「loop内変数とparseコードの型推論が遅い」という報告を受けた実プロファイリング
  調査から、`&a = $a`型のread-modify-write連鎖がsite数に対し超線形
  （6倍入力で約49.6倍）に増悪すると判明。真因は`ProjectionPreflight::
  validate_record`が同一proof structureを毎query完全再走査すること——N=6で
  50,266,205回の呼び出し中、新規展開はわずか0.126%。fresh consequence自体
  （2026-08-04調査のalpha census、926件acceptedかつglobal alpha-equivalent
  ゼロ）は一切削減せず、CPK計画§4のnon-goalと衝突しない形で、(A)admission時に
  一度だけcanonical order/membership/supportを証明するstructural certificate、
  (B)同一snapshot内でのvalidation成功を別preflight roundが再利用する
  snapshot-scoped structural-validity cache、の二段設計を採用。最重要の論点
  ——このcacheがDPN/MPCの禁じる「永続的evaluator memo」と混同されないか——は、
  文書起案を一切知らない独立Codexセッションに具体的反例（`A→B→A`のcycleに
  `A→dangling C`が絡むケース）での反証を依頼し、「HOLDS（正しく遮断される）」
  と確認済み（発見された2点の補強——publication経路をtermination guardから
  分離する実装上の必須事項、この反例形をfixtureとして固定する必要——は
  文書へ反映済み）。実装はCPK-SV-A〜Eの5段階shadow→cutover方式。性能目標は
  保守的にN=6の4.839秒から1〜2秒回収と明記、2.75秒全回収や線形化は保証しない）。
  CPK-SV-A（`f0359890`+`c877bfd2`）、CPK-SV-B（`a333d5d1`+`7e1da8eb`）は各々
  独立review→修正を経て着地・push済み。CPK-SV-Cはclaim/live-row動的依存の
  追跡部分で実装レビュー3回連続HIGH検出（意味identity欠落→非transactional
  reconciliation→逆方向race+silentデータ消失、と深刻度が悪化）という異常事態
  となり、ユーザ判断で実装パッチを止めて設計自体を見直した
- `notes/design/2026-08-13-cpk-sv-c-dynamic-dependency-synchronization-addendum.md`
  （CPK-SV-C追補: dynamic dependencyの単一owner化とlate-bound validation
  obligation・ユーザ承認済み（2026-08-13、rev.2）。著者はCodex gpt-5.6-sol
  （xhigh）が起案、Claude (Sonnet 5)が独立査読・確定。CPK-SV-C（claim move/
  live-row lifecycleが持つcurrent claim location/live-row stateをformula
  adjacencyへ追跡する部分）で3回連続の独立実装レビューがHIGH級バグを検出
  ——1回目: action identity粗結合と依存カテゴリ欠落、2回目: prepare〜commit間
  の非transactional reconciliation+O(N²)走査、3回目（最深刻）: 2回目の修正が
  逆方向race（lifecycle側がformula新規登録を見逃す）を露呈させ、かつstale
  formula commitが`commit_projection_clause_admission`で成否を返さずcaller
  がその後もaccepted扱いで処理を続ける、mandatory proof relationのsilent
  data loss——という、直すたびに同クラスの問題が別箇所に再発するパターンに
  達したため、ユーザが「4回目のパッチではなく設計を見直す」と判断。根因診断
  （Sol起案、Claude査読）: `ValidateBound(current_record)`等が実はformula
  incidenceの不変事実ではなくclaim/live-row authorityのcurrent viewから
  導出される値なのに、それをformula側のpersistent indexへコピーしたことで、
  「formula writerがdynamic authorityのcurrent valueを知る」「dynamic
  authority writerがformula dependentsを知り全コピーを更新する」という
  双方向の知識が同時に必要になった——ownership分裂が本質。解決策（stable
  obligation + authoritative late binding）: formula側は`(representative,
  expected_root)`という不変なfrozen識別子だけを持ち、claim/live-row側は
  formula adjacencyを一切書き換えない。動的事実はquery時にauthorityへ直接
  late-bindして解決する。silent data loss対策として、`Prepared...::
  accepted()`をcommit前後で読めるcontractを廃止し、`Result<CommittedBatch,
  Conflict>`型のcommitでaccepted clausesをsuccessful receiptからしか
  取得できない設計へ。設計自体のsoundnessは、起案を一切知らない別Codex
  セッションによる敵対的reviewで検証済み（判定: SOUND WITH GAPS、3件の
  具体的な穴——(1) `projection_lower_records_by_root`という別目的の生産
  必須reverse mapを誤って「dependent visit 0」に含めていた、(2) formula/
  support-ledger closure（`OrphanFormula`/`MissingProofFact`）の証明が
  抜けていた、(3) canonical fallbackがfrozen/current divergence由来の
  real invariant violationを握り潰しうる非対称性があった——は全てrev.2で
  修正し、Claudeが文書全文を直接読んで最終確認。実装はCPK-SV-C-R0（silent-
  loss barrier、最優先、`b8777d67`+`2341d1a5`）→R1（stable obligation
  shadow、`b2c6eed5`+`f41aea6a`）→R2（cross-writer reverse map撤去、
  `1e9ae94d`+`4e074db0`）→R3（exhaustive closure gate、`771e47d4`+
  `5c72d9f8`+`82768391`）の4段階、全段階が各々独立review→修正のサイクルを
  経て着地・push済み（2026-08-13）。R3だけは独立レビュー3回を要した——1回目
  はタイムアウト復旧の急ぎ修正がread-trace抑制とcheck-state同期を誤って
  結合させる副作用を生み（HIGH2件）、2回目でその修正自体を検証、3回目で
  interleavingフィクスチャがcanonical fallback経由でも見かけ上パスして
  しまう穴（MEDIUM1件、negative controlだけ`!stable.stable_fallback_used`
  を検証してた非対称性）を検出——最終的に3回連続レビューで実バグ・実穴が
  見つかり続けたが、severityはHIGH→HIGH→MEDIUMと収束したため4回目のレビュー
  は見送り、修正内容が最小（assertion追加8行のみ、production code不変）
  かつ実測証拠（fallback 0/108,241件、exhaustive gate全項目mismatch 0）で
  裏付けられた時点でpush判断。CPK-SV-D0（shadow-only structural snapshot
  invalidation census、`251e64a8`+`a88b0257`+`9ce43039`、push済み）に着手し
  たが、exhaustive census gateの正しさを保証する試みが5回連続で同型の
  「vacuous gate」問題（何かが変わったら必ずbumpする、ではなく「何も変わって
  ないと主張する判定」を機械的に検証できない）に当たり、cache本体
  （CPK-SV-D）はユーザ判断で保留。試行順: (1) self-referential
  include_str!検索 (2) mutation class単位のaggregate counter (3)
  per-writer-site counterだが`ProofOccurrence`が複数writerを共有 (4)
  atomic-boundary+shared-sink二軸モデルのdesign addendum草案（独立review
  でNOT SOUND、`ProjectionIndexAdmissionCommit`のtarget/edge branch
  maskingが具体反例） (5) opaque `ProofStructuralState`+sealed gateway+
  exhaustive-match dispatchによる「機械的closure」設計（独立reviewで
  NOT SOUND、command内部のChanged/Unchanged判定自体がcompile-time保証外
  のまま残るという核心的な穴、かつtrusted kernelが実際には数千行規模になる
  との指摘）。(4)(5)ともに未承認draftとして削除済み、正本文書には残さない。
  D0実装自体（snapshot type・saturating advance・19 writer siteタグ付け）
  はshadow-onlyで実害ゼロ、骨格は健全と確認済みのため土台としてpush済みだが、
  cache read pathの再開はユーザの追加承認と、census設計の根本的な再検討が
  前提。詳細な経緯はmemory参照）
- `notes/design/2026-08-13-cpk-sv-d-sealed-conservative-cache-plan.md`
  （CPK-SV-D統合再設計: sealed structural gateway + conservative-default
  cache・rev.9確定・ユーザ承認済み（2026-08-14）。著者はCodex gpt-5.6-sol
  （xhigh）が起案、Claude (Sonnet 5)が独立査読・確定。CPK-SV-D0のcensus
  保留後、実測(RMW N=6でcross-round same-snapshot再検証97.30%、cold
  std::text::parseで26.63%)がcache再検討の価値を裏付けたため、「Unchanged
  を主張するには明示的証明必須、迷ったら常にChanged」という非対称設計
  （round 6）と、「全writerを単一sealed gatewayへ強制通過させる」構造
  （round 5）を統合。round 5とround 6は相補的に失敗した(round 5は
  closureが強くdefaultが弱い、round 6はdefaultが強くclosureが無い)という
  診断のもと、9回の改訂・16回以上の独立レビューを経て確定。rev.4では
  repository外のstandalone prototype（`/tmp/cpk-sv-d-kernel-skeleton`、
  disposable、production非統合）で実際にRustコンパイラへ検証させ
  （E0603/E0451/E0515/E0500/E0501等の実コンパイルエラーを証拠として使用）、
  pseudocodeレビューだけでは決着しなかった型システムレベルの問い
  （panic-unwind時のticket所有権、per-getter RefCell/Cell rechecking
  の不十分性、HRTB exclusive query scopeの有効性等）に決着をつけた。
  round 9で「アーキテクチャの核心は収束、残るのは実装細部」という中間
  評価（本アーク初のSOUND WITH GAPS）を得た後も、round 10〜11で新たな
  実装レベルの穴（round-persistent stateとHRTB scopeの両立、attempt
  identity欠如によるcross-attempt false memo hit等）が見つかり、都度
  narrow revisionで対応。round 11の指摘については専用meta-reviewで
  「型としては実在するがcurrent production call graphには到達不能」と
  判定した上で、ユーザ判断でdefense-in-depthとして修正（rev.6〜rev.9）。
  最終rev.9への独立レビューで初めてfindings ゼロの"READY"判定を獲得し、
  Claude (Sonnet 5)が全3,420行を直接通読して既存正本群との整合性を確認
  した上で確定。実装はSS0(read-only census)〜SS9(closeout)の少なくとも
  9段階、blast radius見積もりは8〜15ファイル・semantic edit 5,000〜
  10,000行・visible diff 9,000〜18,000行超と正直に記載。CPK-SV-A/B/C/D0
  の既存決定は一切変更せず、CPK-SV-Dのsnapshot writer ownership・
  mutation finalization・successful structural-validity cacheだけを
  対象とする）。
  **実装進捗**: SS0（read-only census）は約9分で全writer siteが
  unassigned zeroで完走——5回失敗したD0 censusと対照的にクリーンに
  完走した。続くSS1（sealed shadow kernel）は独立review 4回を要した
  （round 1: 既存test誤破壊＋privacy probe未実装等4件のHIGH検出、
  round 2: multi-domain atomicity race検出、round 3: publication
  phaseにruntime `assert_domain`が残存という設計原則違反を検出——
  ユーザが「しっかり設計から対処しましょう」と表面パッチでなく
  根本修正を明示指示、round 4: `ResourceDomainMarker`による
  compile-time domain保証への刷新で初のfindings ゼロ）。SS1完了後
  SS2着手前にSS7以降のHRTB read-scope基盤（旧SS6所在）とSS2の
  write-authority cutoverの間に、production readerの合法な橋渡しが
  rev.9文書に定義されていないgapが判明——別の signed addendum
  （下記）として解決した。
- `notes/design/2026-08-14-cpk-sv-d-ss2-read-foundation-resequencing-addendum.md`
  （CPK-SV-D SS2 read foundation resequencing addendum・rev.7確定・
  ユーザ承認済み（2026-08-14）。著者はCodex gpt-5.6-sol（xhigh）が起案、
  Claude (Sonnet 5)が独立査読・確定。旧SS6のHRTB exclusive-query-scope
  read基盤をSS2より前に前倒しする（新設スライスSS1-RF、SS2内に
  SS2-P0チェックポイントを追加）resequencing。7回の改訂・7回の独立
  レビューを要し、うち3回が**NOT SOUND**——毎回、以前 shelveした
  CPK-SV-D0（全writerがsnapshotを漏れなくbumpしていることの機械的
  exhaustiveness証明、5回失敗）と同じクラスの壁にぶつかった。
  rev.1: cross-scope round-reuseをD0 snapshotへ依存させる設計が
  NOT SOUND。rev.2: cross-scope reuseをSS5完了（全writer sealed）まで
  遅延させる設計に転換しSOUND WITH GAPS。rev.3: witness token
  導入を試みるも「規約止まりで型的証拠でない」とNOT SOUND。rev.4:
  value-consuming typestate（`ProofAttemptKernel<Layout>`）へ再設計する
  も、CPK-SV-D0のround 5と全く同型の反例——「型は特定の値の所有を
  証明するが、集合のexhaustivenessは証明しない」（`LegacyRowOwner`から
  fieldを漏らしても全transitionがcompileしwitnessが発行される）が
  見つかり3度目のNOT SOUND。ここでユーザが「mechanical closureを
  諦め、D0と同じ形で妥協」と明示決定——rev.5でtypestateを
  「careless premature sealingを防ぐbest-effort guard」へde-scopeし、
  完全性判定はD0と同水準の人手census/test/fault-injection gate
  （§6.2）へ委ねる方針転換。rev.6〜rev.7はcaller matrix・scope境界の
  実務的な穴（`scheme_projection_record_is_included`の別call site2件、
  `capture_generalized_witnesses`等row 1派生4subrowの見落とし等）を
  閉じ、ようやくfindings ゼロ到達。Claude (Sonnet 5)が全1,390行を
  直接通読して確定。**D0の教訓が独立に2度目の再現を見せた**——
  「semantic exhaustivenessをRust型システムだけで機械的に証明する」
  という目標自体が、設計をどう変えても同じ壁に当たる可能性が高いと
  いう経験則が補強された）。
  **実装進捗（SS1-RF、2026-08-14）**: `0ce3a095`で実装着手した直後、
  Codexが正しく「§2.2の`Result<R, ProofFailure>`という exact signature
  と、`ForeignAttemptRoundState`が別型`ProofAccessError`である」という
  未解決の矛盾を発見・停止して報告した。ここでClaudeが「これは軽微な
  実装詳細の精密化」と誤判断し、新しい`ProofQueryError`型を導入して
  delegateの戻り値型を変更することを承認——これは正本のexact signature
  契約を実装の都合で独断変更した規約違反だった（教訓は
  `~/.claude/projects/.../memory/feedback-no-unilateral-signed-doc-deviation.md`
  参照）。独立レビューがHIGHとして検出、`416981b4`でexact signatureへ
  復元（`ProofFailure`側に`ForeignAttemptRoundState`/`TerminalLatchBusy`
  variantを追加）。この修正が新たな意味論バグ——一時的なaccess denial
  がsticky attempt-terminal failureとして誤ってlatchされる——を生み、
  `f8e94588`で`requires_attempt_terminal()`分類により修正。さらにこの
  過程での型移動が`ProofAttemptNonce`のvisibilityを意図せず広げる
  regressionを生み、`70c1b52f`で修正。計5回の独立レビュー・4回の修正
  commitを経てpass、push済み）。
  **実装進捗（SS2-P0基盤、2026-08-14）**: SS1-RF完了後、addendum §4.0.1の
  all-legacy read route（`LegacyOnlyReadSources`、`with_legacy_projection_query`
  / `with_legacy_publication_query`）を実装。ConstraintMachineの実fieldを
  disjoint field-splitでborrowし、closureへ`&ConstraintMachine`を再渡し
  しない設計。3回の独立レビューを経てpass、push済み（`eb7cc48c` feat →
  `44eaf057` fix：`..` catch-allが将来のfield追加を静かに見逃す穴を
  塞ぐ、multi-family seedingテスト強化、re-export surface probeの精密化、
  legacy delegate用foreign-round/retryabilityテスト追加 → `58729db3`
  test：foreign-round regressionテストにsticky failure注入を追加して
  回帰保護を強化）。SS1-RFで見た「HIGH→HIGH→MEDIUM→zero」という収束
  パターンとは異なり、今回はSS1-RFでの判断ミスの反省を踏まえ、
  exact signature確認を最初から明示的に依頼した結果、severityは
  最初から軽微（MEDIUM/LOW止まり）で収束が早かった。次はaddendum
  §4.0.2の7つのproduction caller row（`scheme_projectable_lowers`他、
  `infer/check.rs`・`yulang/source/mod.rs`・`yulang/server.rs`まで
  及ぶcaller-side rewrite）の移行が残っている——SS2-P0本体はまだ未着手）。
  **実装進捗（row2移行、2026-08-14）**: row1のcore helperだけを独立移行
  しようと試みたところ、Codexが「`scheme_projectable_lowers`自体は
  owned result生成ロジックを持たないpure wrapperで、独立した移行単位
  として存在しない」と正しく報告・停止。実consumerは全てrow2
  (`expand_positive_aliases_in_scheme_compact`, `generalize/mod.rs`)
  含む派生caller側にあると判明し、row1とrow2を一体で移行する方針へ
  ユーザ承認を得て転換。row2の実装接触で、rev.7のexact visibility
  （`pub(in crate::constraints)`）が、実際のcaller`generalize/mod.rs`
  （`constraints`の子孫ではなく兄弟モジュール）から構造的に届かない
  という、addendum自身の§3.3が予見していたgapが発覚。addendumを
  rev.8→rev.9として正式改訂（rev.8は「row2が実際に必要とする
  `PosId→TypeVar`変換のsafe methodが列挙から漏れている」というHIGHで
  一度NOT SOUND、rev.9で`pos_var_in_scope`追加により2回のレビューで
  SOUND確定）。可視性の壁を解消した後、row2の`&mut ConstraintMachine`
  要求が`analysis/session/generalize.rs`・`lowering/expr/tail.rs`・
  `lowering/expr/method_body.rs`という「単純なscoped mutable reborrow」
  3箇所と、`check.rs`（`HoverFormatContext`が`&PolyCheckOutput`を保持
  したままmutable machine borrowを跨げない、という構造的な分割が必要）
  経由で`yulang/src/source/mod.rs`・`server.rs`のhover/completion
  entrypointまで波及するmutable-owner cascadeとして実装（ユーザが
  「cascade全体をscopeに含めて引き続き進める」と明示承認）。全体で
  7コミット（`d3b6c3ca` feat：scope-local API追加 → `6a9fa0b8` docs：
  addendum rev.9確定 → `0478dd19` refactor：row2本体+mutable-owner
  cascade全体+census/inventory manifestの追随漏れ2件修正（既知の
  pre-existing failure 1件を除き全green）→ `9d14f9d6` fix：独立
  レビューが指摘したMEDIUM（final sealed cutover facadeの可視性拡大
  漏れ）とLOW（hover/completionのclone順序、filter前にcloneしていた
  ため元のstreaming挙動へ復元）→ `2da1655a` chore：final facadeの
  意図的dead_code警告を抑制）で完走・push済み。途中、`yulang`の
  `source::`テストが90分ハングしたように見えメモリも増加傾向を示した
  ため一旦プロセスをkillして調査したが、bounded/individual test run
  （`timeout 60s`・`--test-threads=1`）で検証した結果、修正コード
  自体（hover/completion）は無罪——`source::`という広いフィルタが
  std読み込みを伴う無関係な重いVM/mono/evidence実行テストまで243件
  まとめて拾い、`--test-threads=4`で並列実行したことが原因のfalse
  alarmと確認できた。残るはaddendum §4.0.2のrow3〜7の移行）
